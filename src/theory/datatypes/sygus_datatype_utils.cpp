/*********************                                                        */
/*! \file sygus_datatype_utils.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of rewriter for the theory of (co)inductive datatypes.
 **
 ** Implementation of rewriter for the theory of (co)inductive datatypes.
 **/

#include "theory/datatypes/sygus_datatype_utils.h"

#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "expr/sygus_datatype.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/evaluator.h"
#include "theory/rewriter.h"

using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace datatypes {
namespace utils {

Node applySygusArgs(const DType& dt,
                    Node op,
                    Node n,
                    const std::vector<Node>& args)
{
  if (n.getKind() == BOUND_VARIABLE)
  {
    Assert(n.hasAttribute(SygusVarNumAttribute()));
    int vn = n.getAttribute(SygusVarNumAttribute());
    Assert(dt.getSygusVarList()[vn] == n);
    return args[vn];
  }
  // n is an application of operator op.
  // We must compute the free variables in op to determine if there are
  // any substitutions we need to make to n.
  TNode val;
  if (!op.hasAttribute(SygusVarFreeAttribute()))
  {
    std::unordered_set<Node, NodeHashFunction> fvs;
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

struct SygusOpRewrittenAttributeId
{
};
typedef expr::Attribute<SygusOpRewrittenAttributeId, Node>
    SygusOpRewrittenAttribute;

Kind getEliminateKind(Kind ok)
{
  Kind nk = ok;
  // We also must ensure that builtin operators which are eliminated
  // during expand definitions are replaced by the proper operator.
  if (ok == BITVECTOR_UDIV)
  {
    nk = BITVECTOR_UDIV_TOTAL;
  }
  else if (ok == BITVECTOR_UREM)
  {
    nk = BITVECTOR_UREM_TOTAL;
  }
  else if (ok == DIVISION)
  {
    nk = DIVISION_TOTAL;
  }
  else if (ok == INTS_DIVISION)
  {
    nk = INTS_DIVISION_TOTAL;
  }
  else if (ok == INTS_MODULUS)
  {
    nk = INTS_MODULUS_TOTAL;
  }
  return nk;
}

Node eliminatePartialOperators(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.push_back(cur);
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      Kind ok = cur.getKind();
      Kind nk = getEliminateKind(ok);
      if (nk != ok || childChanged)
      {
        ret = nm->mkNode(nk, children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
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
    // expanding definitions, rewriting it, and eliminating partial operators.
    if (!op.hasAttribute(SygusOpRewrittenAttribute()))
    {
      if (op.isConst())
      {
        // If it is a builtin operator, convert to total version if necessary.
        // First, get the kind for the operator.
        Kind ok = NodeManager::operatorToKind(op);
        Trace("sygus-grammar-normalize-debug")
            << "...builtin kind is " << ok << std::endl;
        Kind nk = getEliminateKind(ok);
        if (nk != ok)
        {
          Trace("sygus-grammar-normalize-debug")
              << "...replace by builtin operator " << nk << std::endl;
          opn = NodeManager::currentNM()->operatorOf(nk);
        }
      }
      else
      {
        // Only expand definitions if the operator is not constant, since
        // calling expandDefinitions on them should be a no-op. This check
        // ensures we don't try to expand e.g. bitvector extract operators,
        // whose type is undefined, and thus should not be passed to
        // expandDefinitions.
        opn = smt::currentSmtEngine()->expandDefinitions(op);
        opn = Rewriter::rewrite(opn);
        opn = eliminatePartialOperators(opn);
        SygusOpRewrittenAttribute sora;
        op.setAttribute(sora, opn);
      }
    }
    else
    {
      opn = op.getAttribute(SygusOpRewrittenAttribute());
    }
  }
  return mkSygusTerm(opn, children, doBetaReduction);
}

Node mkSygusTerm(Node op,
                 const std::vector<Node>& children,
                 bool doBetaReduction)
{
  Trace("dt-sygus-util") << "Operator is " << op << std::endl;
  if (children.empty())
  {
    // no children, return immediately
    Trace("dt-sygus-util") << "...return direct op" << std::endl;
    return op;
  }
  // if it is the any constant, we simply return the child
  if (op.getAttribute(SygusAnyConstAttribute()))
  {
    Assert(children.size() == 1);
    return children[0];
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
    ret = NodeManager::currentNM()->mkNode(op, schildren);
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
    ret = NodeManager::currentNM()->mkNode(otk, schildren);
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
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
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

Node sygusToBuiltinEval(Node n, const std::vector<Node>& args)
{
  NodeManager* nm = NodeManager::currentNM();
  Evaluator eval;
  // constant arguments?
  bool constArgs = true;
  for (const Node& a : args)
  {
    if (!a.isConst())
    {
      constArgs = false;
      break;
    }
  }
  std::vector<Node> eargs;
  bool svarsInit = false;
  std::vector<Node> svars;
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
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
      TypeNode tn = cur.getType();
      if (!tn.isDatatype() || !tn.getDType().isSygus())
      {
        visited[cur] = cur;
      }
      else if (cur.isConst())
      {
        // convert to builtin term
        Node bt = sygusToBuiltin(cur);
        // run the evaluator if possible
        if (!svarsInit)
        {
          svarsInit = true;
          TypeNode type = cur.getType();
          Node varList = type.getDType().getSygusVarList();
          for (const Node& v : varList)
          {
            svars.push_back(v);
          }
        }
        Assert(args.size() == svars.size());
        // try evaluation if we have constant arguments
        Node ret = constArgs ? eval.eval(bt, svars, args) : Node::null();
        if (ret.isNull())
        {
          // if evaluation was not available, use a substitution
          ret = bt.substitute(
              svars.begin(), svars.end(), args.begin(), args.end());
        }
        visited[cur] = ret;
      }
      else
      {
        if (cur.getKind() == APPLY_CONSTRUCTOR)
        {
          visited[cur] = Node::null();
          visit.push_back(cur);
          for (const Node& cn : cur)
          {
            visit.push_back(cn);
          }
        }
        else
        {
          // it is the evaluation of this term on the arguments
          if (eargs.empty())
          {
            eargs.push_back(cur);
            eargs.insert(eargs.end(), args.begin(), args.end());
          }
          else
          {
            eargs[0] = cur;
          }
          visited[cur] = nm->mkNode(DT_SYGUS_EVAL, eargs);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      Assert(cur.getKind() == APPLY_CONSTRUCTOR);
      const DType& dt = cur.getType().getDType();
      // non sygus-datatype terms are also themselves
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
        // apply to arguments
        ret = mkSygusTerm(dt, index, children);
      }
      visited[cur] = ret;
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

void getFreeSymbolsSygusType(TypeNode sdt,
                             std::unordered_set<Node, NodeHashFunction>& syms)
{
  // datatype types we need to process
  std::vector<TypeNode> typeToProcess;
  // datatype types we have processed
  std::map<TypeNode, TypeNode> typesProcessed;
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
  std::set<TypeNode> unres;

  Trace("dtsygus-gen-debug") << "Process sygus type:" << std::endl;
  Trace("dtsygus-gen-debug") << sdtd.getName() << std::endl;

  // datatype types we need to process
  std::vector<TypeNode> dtToProcess;
  // datatype types we have processed
  std::map<TypeNode, TypeNode> dtProcessed;
  dtToProcess.push_back(sdt);
  std::stringstream ssutn0;
  ssutn0 << sdtd.getName() << "_s";
  TypeNode abdTNew =
      nm->mkSort(ssutn0.str(), ExprManager::SORT_FLAG_PLACEHOLDER);
  unres.insert(abdTNew);
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
          std::map<TypeNode, TypeNode>::iterator itdp = dtProcessed.find(argt);
          TypeNode argtNew;
          if (itdp == dtProcessed.end())
          {
            std::stringstream ssutn;
            ssutn << argt.getDType().getName() << "_s";
            argtNew =
                nm->mkSort(ssutn.str(), ExprManager::SORT_FLAG_PLACEHOLDER);
            Trace("dtsygus-gen-debug") << "    ...unresolved type " << argtNew
                                       << " for " << argt << std::endl;
            unres.insert(argtNew);
            dtProcessed[argt] = argtNew;
            dtNextToProcess.push_back(argt);
          }
          else
          {
            argtNew = itdp->second;
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
  std::vector<TypeNode> datatypeTypes = nm->mkMutualDatatypeTypes(
      datatypes, unres, NodeManager::DATATYPE_FLAG_PLACEHOLDER);
  TypeNode sdtS = datatypeTypes[0];
  if (Trace.isOn("dtsygus-gen-debug"))
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

}  // namespace utils
}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4
