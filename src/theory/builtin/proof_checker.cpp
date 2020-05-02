/*********************                                                        */
/*! \file proof_checker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of equality proof checker
 **/

#include "theory/builtin/proof_checker.h"

#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace builtin {

Node BuiltinProofRuleChecker::applyRewrite(Node n)
{
  return Rewriter::rewrite(n);
}

Node BuiltinProofRuleChecker::applyRewriteEqualityExt(Node n)
{
  return Rewriter::rewriteEqualityExt(n);
}

Node BuiltinProofRuleChecker::applySubstitution(Node n, Node exp)
{
  if (exp.isNull() || exp.getKind() != EQUAL)
  {
    return Node::null();
  }
  TNode var = exp[0];
  TNode subs = exp[1];
  return n.substitute(var, subs);
}

Node BuiltinProofRuleChecker::applySubstitution(Node n,
                                                const std::vector<Node>& exp)
{
  Node curr = n;
  // apply substitution one at a time
  for (const Node& e : exp)
  {
    curr = applySubstitution(curr, e);
    if (curr.isNull())
    {
      return Node::null();
    }
  }
  return curr;
}

Node BuiltinProofRuleChecker::applySubstitutionRewrite(
    Node n, const std::vector<Node>& exp)
{
  Node ret = applySubstitution(n, exp);
  ret = applyRewrite(ret);
  return ret;
}

Node BuiltinProofRuleChecker::checkInternal(PfRule id,
                                            const std::vector<Node>& children,
                                            const std::vector<Node>& args)
{
  // compute what was proven
  if (id == PfRule::ASSUME)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getType().isBoolean());
    return args[0];
  }
  else if (id == PfRule::SCOPE)
  {
    Assert(children.size() == 1);
    if (args.empty())
    {
      // no antecedant
      return children[0];
    }
    Node ant = mkAnd(args);
    // if the conclusion is false, its the negated antencedant only
    if (children[0].isConst() && !children[0].getConst<bool>())
    {
      return NodeManager::currentNM()->mkNode(NOT, ant);
    }
    return NodeManager::currentNM()->mkNode(IMPLIES, ant, children[0]);
  }
  else if (id == PfRule::SUBS)
  {
    Assert(children.size() > 0);
    Assert(args.size() == 1);
    std::vector<Node> exp;
    for (size_t i = 0, nchild = children.size(); i < nchild; i++)
    {
      exp.push_back(children[i]);
    }
    Node res = applySubstitution(args[0], exp);
    return args[0].eqNode(res);
  }
  else if (id == PfRule::REWRITE)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node res = applyRewrite(args[0]);
    return args[0].eqNode(res);
  }
  /*
  else if (id == PfRule::REWRITE_EQ_EXT)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node res = applyRewriteEqualityExt(args[0]);
    return args[0].eqNode(res);
  }
  */
  else if (id == PfRule::SUBS_REWRITE)
  {
    // FIXME: could be macro
    // (TRANS (SUBS P1 ... Pn t)
    //        (REWRITE <t.substitute(xn,tn). ... .substitute(x1,t1)>))
    Assert(args.size() == 1);
    std::vector<Node> exp = children;
    std::reverse(exp.begin(), exp.end());
    Node res = applySubstitutionRewrite(args[0], exp);
    return args[0].eqNode(res);
  }
  else if (id == PfRule::SUBS_REWRITE_PRED)
  {
    Assert(args.size() == 1);
    std::vector<Node> exp = children;
    std::reverse(exp.begin(), exp.end());
    Node res = applySubstitutionRewrite(args[0], exp);
    if (!res.isConst() || !res.getConst<bool>())
    {
      return Node::null();
    }
    return args[0];
  }
  // no rule
  return Node::null();
}

}  // namespace builtin
}  // namespace theory
}  // namespace CVC4
