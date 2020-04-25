/*********************                                                        */
/*! \file sygus_datatype_utils.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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
#include "theory/datatypes/theory_datatypes_utils.h"
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
  TypeNode tn = op.getType();
  if (tn.isConstructor())
  {
    return APPLY_CONSTRUCTOR;
  }
  else if (tn.isSelector())
  {
    return APPLY_SELECTOR;
  }
  else if (tn.isTester())
  {
    return APPLY_TESTER;
  }
  else if (tn.isFunction())
  {
    return APPLY_UF;
  }
  return UNDEFINED_KIND;
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
        opn = Node::fromExpr(
            smt::currentSmtEngine()->expandDefinitions(op.toExpr()));
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

Node sygusToBuiltin(Node n, bool isExternal)
{
  Assert(n.isConst());
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

}  // namespace utils
}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4
