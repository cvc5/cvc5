/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of rewriter for the theory of (co)inductive datatypes.
 */

#include "theory/datatypes/sygus_datatype_utils.h"

#include <sstream>

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/sygus_datatype.h"
#include "smt/env.h"
#include "theory/evaluator.h"
#include "theory/rewriter.h"

using namespace cvc5::internal;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace datatypes {
namespace utils {

Node applySygusArgs(const DType& dt,
                    Node op,
                    Node n,
                    const std::vector<Node>& args)
{
  // optimization: if n is just a sygus bound variable, return immediately
  // by replacing with the proper argument, or returning unchanged if it is
  // a bound variable not corresponding to a formal argument.
  if (n.getKind() == BOUND_VARIABLE)
  {
    if (n.hasAttribute(SygusVarNumAttribute()))
    {
      int vn = n.getAttribute(SygusVarNumAttribute());
      Assert(dt.getSygusVarList()[vn] == n);
      return args[vn];
    }
    // it is a different bound variable, it is unchanged
    return n;
  }
  // n is an application of operator op.
  // We must compute the free variables in op to determine if there are
  // any substitutions we need to make to n.
  TNode val;
  if (!op.hasAttribute(SygusVarFreeAttribute()))
  {
    std::unordered_set<Node> fvs;
    if (expr::getFreeVariables(op, fvs))
    {
      if (fvs.size() == 1)
      {
        for (const Node& v : fvs)
        {
          val = v;
        }
      }
      else
      {
        val = op;
      }
    }
    Trace("dt-sygus-fv") << "Free var in " << op << " : " << val << std::endl;
    op.setAttribute(SygusVarFreeAttribute(), val);
  }
  else
  {
    val = op.getAttribute(SygusVarFreeAttribute());
  }
  if (val.isNull())
  {
    return n;
  }
  if (val.getKind() == BOUND_VARIABLE)
  {
    // single substitution case
    int vn = val.getAttribute(SygusVarNumAttribute());
    TNode sub = args[vn];
    return n.substitute(val, sub);
  }
  // do the full substitution
  std::vector<Node> vars;
  Node bvl = dt.getSygusVarList();
  for (unsigned i = 0, nvars = bvl.getNumChildren(); i < nvars; i++)
  {
    vars.push_back(bvl[i]);
  }
  return n.substitute(vars.begin(), vars.end(), args.begin(), args.end());
}

Kind getOperatorKindForSygusBuiltin(Node op)
{
  Assert(op.getKind() != BUILTIN);
  if (op.getKind() == LAMBDA)
  {
    return APPLY_UF;
  }
  return NodeManager::getKindForFunction(op);
}

Node mkSygusTerm(const DType& dt,
                 unsigned i,
                 const std::vector<Node>& children,
                 bool doBetaReduction,
                 bool isExternal)
{
  Trace("dt-sygus-util") << "Make sygus term " << dt.getName() << "[" << i
                         << "] with children: " << children << std::endl;
  Assert(i < dt.getNumConstructors());
  Assert(dt.isSygus());
  Assert(!dt[i].getSygusOp().isNull());
  Node op = dt[i].getSygusOp();
  Node opn = op;
  if (!isExternal)
  {
    // Get the normalized version of the sygus operator. We do this by
    // expanding definitions.
    if (!op.isConst())
    {
      // Get the expanded definition form, if it has been marked. This ensures
      // that user-defined functions have been eliminated from op.
      opn = getExpandedDefinitionForm(op);
    }
  }
  // if it is the any constant, we simply return the child
  if (dt[i].isSygusAnyConstant())
  {
    Assert(children.size() == 1);
    return children[0];
  }
  Node ret = mkSygusTerm(opn, children, doBetaReduction);
  Assert(ret.getType() == dt.getSygusType());
  return ret;
}

Node mkSygusTerm(const Node& op,
                 const std::vector<Node>& children,
                 bool doBetaReduction)
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(nm->getSkolemManager()->getId(op) != SkolemFunId::SYGUS_ANY_CONSTANT);
  Trace("dt-sygus-util") << "Operator is " << op << std::endl;
  if (children.empty())
  {
    // no children, return immediately
    Trace("dt-sygus-util") << "...return direct op" << std::endl;
    return op;
  }
  std::vector<Node> schildren;
  // get the kind of the operator
  Kind ok = op.getKind();
  if (ok != BUILTIN)
  {
    if (ok == LAMBDA && doBetaReduction)
    {
      // Do immediate beta reduction. It suffices to use a normal substitution
      // since neither op nor children have quantifiers, since they are
      // generated by sygus grammars.
      std::vector<Node> vars{op[0].begin(), op[0].end()};
      Assert(vars.size() == children.size());
      Node ret = op[1].substitute(
          vars.begin(), vars.end(), children.begin(), children.end());
      Trace("dt-sygus-util") << "...return (beta-reduce) " << ret << std::endl;
      return ret;
    }
    else
    {
      schildren.push_back(op);
    }
  }
  schildren.insert(schildren.end(), children.begin(), children.end());
  Node ret;
  if (ok == BUILTIN)
  {
    ret = nm->mkNode(op, schildren);
    Trace("dt-sygus-util") << "...return (builtin) " << ret << std::endl;
    return ret;
  }
  // get the kind used for applying op
  Kind otk = NodeManager::operatorToKind(op);
  Trace("dt-sygus-util") << "operator kind is " << otk << std::endl;
  if (otk != UNDEFINED_KIND)
  {
    // If it is an APPLY_UF operator, we should have at least an operator and
    // a child.
    Assert(otk != APPLY_UF || schildren.size() != 1);
    ret = nm->mkNode(otk, schildren);
    Trace("dt-sygus-util") << "...return (op) " << ret << std::endl;
    return ret;
  }
  Kind tok = getOperatorKindForSygusBuiltin(op);
  if (schildren.size() == 1 && tok == UNDEFINED_KIND)
  {
    ret = schildren[0];
  }
  else
  {
    ret = NodeManager::currentNM()->mkNode(tok, schildren);
  }
  Trace("dt-sygus-util") << "...return " << ret << std::endl;
  return ret;
}

struct SygusToBuiltinTermAttributeId
{
};
typedef expr::Attribute<SygusToBuiltinTermAttributeId, Node>
    SygusToBuiltinTermAttribute;

// A variant of the above attribute for cases where we introduce a fresh
// variable. This is to support sygusToBuiltin on non-constant sygus terms,
// where sygus variables should be mapped to canonical builtin variables.
// It is important to cache this so that sygusToBuiltin is deterministic.
struct SygusToBuiltinVarAttributeId
{
};
typedef expr::Attribute<SygusToBuiltinVarAttributeId, Node>
    SygusToBuiltinVarAttribute;

// A variant of the above attribute for cases where we introduce a fresh
// variable. This is to support sygusToBuiltin on non-constant sygus terms,
// where sygus variables should be mapped to canonical builtin variables.
// It is important to cache this so that sygusToBuiltin is deterministic.
struct BuiltinVarToSygusAttributeId
{
};
typedef expr::Attribute<BuiltinVarToSygusAttributeId, Node>
    BuiltinVarToSygusAttribute;

Node sygusToBuiltin(Node n, bool isExternal)
{
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  unsigned index;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      // Notice this condition succeeds in roughly 99% of the executions of this
      // method (based on our coverage tests), hence the else if / else cases
      // below do not significantly impact performance.
      if (cur.getKind() == APPLY_CONSTRUCTOR)
      {
        if (!isExternal && cur.hasAttribute(SygusToBuiltinTermAttribute()))
        {
          visited[cur] = cur.getAttribute(SygusToBuiltinTermAttribute());
        }
        else
        {
          visited[cur] = Node::null();
          visit.push_back(cur);
          for (const Node& cn : cur)
          {
            visit.push_back(cn);
          }
        }
      }
      else if (cur.getType().isSygusDatatype())
      {
        Assert (cur.isVar());
        if (cur.hasAttribute(SygusToBuiltinVarAttribute()))
        {
          // use the previously constructed variable for it
          visited[cur] = cur.getAttribute(SygusToBuiltinVarAttribute());
        }
        else
        {
          std::stringstream ss;
          ss << cur;
          const DType& dt = cur.getType().getDType();
          // make a fresh variable
          NodeManager * nm = NodeManager::currentNM();
          Node var = nm->mkBoundVar(ss.str(), dt.getSygusType());
          SygusToBuiltinVarAttribute stbv;
          cur.setAttribute(stbv, var);
          visited[cur] = var;
          // create backwards mapping
          BuiltinVarToSygusAttribute bvtsa;
          var.setAttribute(bvtsa, cur);
        }
      }
      else
      {
        // non-datatypes are themselves
        visited[cur] = cur;
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      Assert(cur.getKind() == APPLY_CONSTRUCTOR);
      const DType& dt = cur.getType().getDType();
      // Non sygus-datatype terms are also themselves. Notice we treat the
      // case of non-sygus datatypes this way since it avoids computing
      // the type / datatype of the node in the pre-traversal above. The
      // case of non-sygus datatypes is very rare, so the extra addition to
      // visited is justified performance-wise.
      if (dt.isSygus())
      {
        std::vector<Node> children;
        for (const Node& cn : cur)
        {
          it = visited.find(cn);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          children.push_back(it->second);
        }
        index = indexOf(cur.getOperator());
        ret = mkSygusTerm(dt, index, children, true, isExternal);
      }
      visited[cur] = ret;
      // cache
      if (!isExternal)
      {
        SygusToBuiltinTermAttribute stbt;
        cur.setAttribute(stbt, ret);
      }
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node builtinVarToSygus(Node v)
{
  BuiltinVarToSygusAttribute bvtsa;
  if (v.hasAttribute(bvtsa))
  {
    return v.getAttribute(bvtsa);
  }
  return Node::null();
}

void getFreeSymbolsSygusType(TypeNode sdt, std::unordered_set<Node>& syms)
{
  // datatype types we need to process
  std::vector<TypeNode> typeToProcess;
  // datatype types we have processed
  std::unordered_set<TypeNode> typesProcessed;
  typeToProcess.push_back(sdt);
  while (!typeToProcess.empty())
  {
    std::vector<TypeNode> typeNextToProcess;
    for (const TypeNode& curr : typeToProcess)
    {
      Assert(curr.isDatatype() && curr.getDType().isSygus());
      const DType& dtc = curr.getDType();
      for (unsigned j = 0, ncons = dtc.getNumConstructors(); j < ncons; j++)
      {
        // collect the symbols from the operator
        Node op = dtc[j].getSygusOp();
        expr::getSymbols(op, syms);
        // traverse the argument types
        for (unsigned k = 0, nargs = dtc[j].getNumArgs(); k < nargs; k++)
        {
          TypeNode argt = dtc[j].getArgType(k);
          if (!argt.isDatatype() || !argt.getDType().isSygus())
          {
            // not a sygus datatype
            continue;
          }
          if (typesProcessed.find(argt) == typesProcessed.end())
          {
            typesProcessed.insert(argt);
            typeNextToProcess.push_back(argt);
          }
        }
      }
    }
    typeToProcess.clear();
    typeToProcess.insert(typeToProcess.end(),
                         typeNextToProcess.begin(),
                         typeNextToProcess.end());
  }
}

TypeNode substituteAndGeneralizeSygusType(TypeNode sdt,
                                          const std::vector<Node>& syms,
                                          const std::vector<Node>& vars)
{
  NodeManager* nm = NodeManager::currentNM();
  const DType& sdtd = sdt.getDType();
  // compute the new formal argument list
  std::vector<Node> formalVars;
  Node prevVarList = sdtd.getSygusVarList();
  if (!prevVarList.isNull())
  {
    for (const Node& v : prevVarList)
    {
      // if it is not being replaced
      if (std::find(syms.begin(), syms.end(), v) != syms.end())
      {
        formalVars.push_back(v);
      }
    }
  }
  for (const Node& v : vars)
  {
    if (v.getKind() == BOUND_VARIABLE)
    {
      formalVars.push_back(v);
    }
  }
  // make the sygus variable list for the formal argument list
  Node abvl = nm->mkNode(BOUND_VAR_LIST, formalVars);
  Trace("sygus-abduct-debug") << "...finish" << std::endl;

  // must convert all constructors to version with variables in "vars"
  std::vector<SygusDatatype> sdts;

  Trace("dtsygus-gen-debug") << "Process sygus type:" << std::endl;
  Trace("dtsygus-gen-debug") << sdtd.getName() << std::endl;

  // datatype types we need to process
  std::vector<TypeNode> dtToProcess;
  // datatype types we have processed
  std::map<TypeNode, TypeNode> dtProcessed;
  dtToProcess.push_back(sdt);
  std::stringstream ssutn0;
  ssutn0 << sdtd.getName() << "_s";
  TypeNode abdTNew = nm->mkUnresolvedDatatypeSort(ssutn0.str());
  dtProcessed[sdt] = abdTNew;

  // We must convert all symbols in the sygus datatype type sdt to
  // apply the substitution { syms -> vars }, where syms is the free
  // variables of the input problem, and vars is the formal argument list
  // of the function-to-synthesize.

  // We are traversing over the subfield types of the datatype to convert
  // them into the form described above.
  while (!dtToProcess.empty())
  {
    std::vector<TypeNode> dtNextToProcess;
    for (const TypeNode& curr : dtToProcess)
    {
      Assert(curr.isDatatype() && curr.getDType().isSygus());
      const DType& dtc = curr.getDType();
      std::stringstream ssdtn;
      ssdtn << dtc.getName() << "_s";
      sdts.push_back(SygusDatatype(ssdtn.str()));
      Trace("dtsygus-gen-debug")
          << "Process datatype " << sdts.back().getName() << "..." << std::endl;
      for (unsigned j = 0, ncons = dtc.getNumConstructors(); j < ncons; j++)
      {
        Node op = dtc[j].getSygusOp();
        // apply the substitution to the argument
        Node ops =
            op.substitute(syms.begin(), syms.end(), vars.begin(), vars.end());
        Trace("dtsygus-gen-debug") << "  Process constructor " << op << " / "
                                   << ops << "..." << std::endl;
        std::vector<TypeNode> cargs;
        for (unsigned k = 0, nargs = dtc[j].getNumArgs(); k < nargs; k++)
        {
          TypeNode argt = dtc[j].getArgType(k);
          TypeNode argtNew;
          if (argt.isDatatype() && argt.getDType().isSygus())
          {
            std::map<TypeNode, TypeNode>::iterator itdp =
                dtProcessed.find(argt);
            if (itdp == dtProcessed.end())
            {
              std::stringstream ssutn;
              ssutn << argt.getDType().getName() << "_s";
              argtNew = nm->mkUnresolvedDatatypeSort(ssutn.str());
              Trace("dtsygus-gen-debug") << "    ...unresolved type " << argtNew
                                         << " for " << argt << std::endl;
              dtProcessed[argt] = argtNew;
              dtNextToProcess.push_back(argt);
            }
            else
            {
              argtNew = itdp->second;
            }
          }
          else
          {
            argtNew = argt;
          }
          Trace("dtsygus-gen-debug")
              << "    Arg #" << k << ": " << argtNew << std::endl;
          cargs.push_back(argtNew);
        }
        std::stringstream ss;
        ss << ops.getKind();
        Trace("dtsygus-gen-debug") << "Add constructor : " << ops << std::endl;
        sdts.back().addConstructor(ops, ss.str(), cargs);
      }
      Trace("dtsygus-gen-debug")
          << "Set sygus : " << dtc.getSygusType() << " " << abvl << std::endl;
      TypeNode stn = dtc.getSygusType();
      sdts.back().initializeDatatype(
          stn, abvl, dtc.getSygusAllowConst(), dtc.getSygusAllowAll());
    }
    dtToProcess.clear();
    dtToProcess.insert(
        dtToProcess.end(), dtNextToProcess.begin(), dtNextToProcess.end());
  }
  Trace("dtsygus-gen-debug")
      << "Make " << sdts.size() << " datatype types..." << std::endl;
  // extract the datatypes
  std::vector<DType> datatypes;
  for (unsigned i = 0, ndts = sdts.size(); i < ndts; i++)
  {
    datatypes.push_back(sdts[i].getDatatype());
  }
  // make the datatype types
  std::vector<TypeNode> datatypeTypes = nm->mkMutualDatatypeTypes(datatypes);
  TypeNode sdtS = datatypeTypes[0];
  if (TraceIsOn("dtsygus-gen-debug"))
  {
    Trace("dtsygus-gen-debug") << "Made datatype types:" << std::endl;
    for (unsigned j = 0, ndts = datatypeTypes.size(); j < ndts; j++)
    {
      const DType& dtj = datatypeTypes[j].getDType();
      Trace("dtsygus-gen-debug") << "#" << j << ": " << dtj << std::endl;
      for (unsigned k = 0, ncons = dtj.getNumConstructors(); k < ncons; k++)
      {
        for (unsigned l = 0, nargs = dtj[k].getNumArgs(); l < nargs; l++)
        {
          if (!dtj[k].getArgType(l).isDatatype())
          {
            Trace("dtsygus-gen-debug")
                << "Argument " << l << " of " << dtj[k]
                << " is not datatype : " << dtj[k].getArgType(l) << std::endl;
            AlwaysAssert(false);
          }
        }
      }
    }
  }
  return sdtS;
}

TypeNode generalizeSygusType(TypeNode sdt)
{
  std::unordered_set<Node> syms;
  getFreeSymbolsSygusType(sdt, syms);
  if (syms.empty())
  {
    return sdt;
  }
  std::vector<Node> svec;
  std::vector<Node> vars;
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& s : syms)
  {
    svec.push_back(s);
    vars.push_back(nm->mkBoundVar(s.getName(), s.getType()));
  }
  return substituteAndGeneralizeSygusType(sdt, svec, vars);
}

unsigned getSygusTermSize(Node n)
{
  if (n.getKind() != APPLY_CONSTRUCTOR)
  {
    return 0;
  }
  unsigned sum = 0;
  for (const Node& nc : n)
  {
    sum += getSygusTermSize(nc);
  }
  const DType& dt = datatypeOf(n.getOperator());
  int cindex = indexOf(n.getOperator());
  Assert(cindex >= 0 && static_cast<size_t>(cindex) < dt.getNumConstructors());
  unsigned weight = dt[cindex].getWeight();
  return weight + sum;
}

/**
 * Map terms to the result of expand definitions calling smt::expandDefinitions
 * on it.
 */
struct SygusExpDefFormAttributeId
{
};
typedef expr::Attribute<SygusExpDefFormAttributeId, Node>
    SygusExpDefFormAttribute;

void setExpandedDefinitionForm(Node op, Node eop)
{
  op.setAttribute(SygusExpDefFormAttribute(), eop);
}

Node getExpandedDefinitionForm(Node op)
{
  Node eop = op.getAttribute(SygusExpDefFormAttribute());
  // if not set, assume original
  return eop.isNull() ? op : eop;
}

}  // namespace utils
}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal
