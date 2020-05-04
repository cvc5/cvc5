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

#include "expr/proof_skolem_cache.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace builtin {
  
const char* toString(RewriterId id)
{
  switch (id)
  {
    case RewriterId::REWRITE: return "REWRITE";
    case RewriterId::REWRITE_EQ_EXT: return "REWRITE_EQ_EXT";
    case RewriterId::IDENTITY: return "IDENTITY";
    default:
      return "RewriterId::Unknown";
  };
  
}

std::ostream& operator<<(std::ostream& out, RewriterId id)
{
  out << toString(id);
  return out;
}

Node BuiltinProofRuleChecker::applyRewrite(Node n, RewriterId id)
{
  Node nk = ProofSkolemCache::getSkolemForm(n);
  Node nkr = applyRewriteExternal(n, id);
  return ProofSkolemCache::getWitnessForm(nkr);
}

Node BuiltinProofRuleChecker::applySubstitution(Node n, Node exp)
{
  if (exp.isNull() || exp.getKind() != EQUAL)
  {
    return Node::null();
  }
  Node nk = ProofSkolemCache::getSkolemForm(n);
  Node nks = applySubstitutionExternal(nk, exp);
  return ProofSkolemCache::getWitnessForm(nks);
}

Node BuiltinProofRuleChecker::applySubstitution(Node n,
                                                const std::vector<Node>& exp)
{
  Node nk = ProofSkolemCache::getSkolemForm(n);
  Node nks = applySubstitutionExternal(nk, exp);
  return ProofSkolemCache::getWitnessForm(nks);
}

Node BuiltinProofRuleChecker::applySubstitutionRewrite(
    Node n, const std::vector<Node>& exp, RewriterId id)
{
  Node nk = ProofSkolemCache::getSkolemForm(n);
  Node nks = applySubstitutionExternal(nk, exp);
  Node nksr = applyRewriteExternal(nks, id);
  return ProofSkolemCache::getWitnessForm(nksr);
}

Node BuiltinProofRuleChecker::applyRewriteExternal(Node n, RewriterId id)
{
  Trace("builtin-pfcheck-debug")
      << "applyRewriteExternal (" << id << "): " << n << std::endl;
  // index determines the kind of rewriter
  if (id == RewriterId::REWRITE)
  {
    return Rewriter::rewrite(n);
  }
  else if (id == RewriterId::REWRITE_EQ_EXT)
  {
    return Rewriter::rewriteEqualityExt(n);
  }
  else if (id == RewriterId::IDENTITY)
  {
    // does nothing
    return n;
  }
  // unknown rewriter
  Assert(false)
      << "BuiltinProofRuleChecker::applyRewriteExternal: no rewriter for " << id
      << std::endl;
  return n;
}

Node BuiltinProofRuleChecker::applySubstitutionExternal(Node n, Node exp)
{
  Assert(!exp.isNull() && exp.getKind() == EQUAL);
  Node expk = ProofSkolemCache::getSkolemForm(exp);
  TNode var = expk[0];
  TNode subs = expk[1];
  return n.substitute(var, subs);
}

Node BuiltinProofRuleChecker::applySubstitutionExternal(
    Node n, const std::vector<Node>& exp)
{
  Node curr = n;
  // apply substitution one at a time, in reverse order
  for (size_t i = 0, nexp = exp.size(); i < nexp; i++)
  {
    if (exp[nexp - 1 - i].isNull() || exp[nexp - 1 - i].getKind() != EQUAL)
    {
      return Node::null();
    }
    curr = applySubstitutionExternal(curr, exp[nexp - 1 - i]);
  }
  return curr;
}

bool BuiltinProofRuleChecker::getRewriterId(TNode n, RewriterId& i)
{
  uint32_t index;
  if (!getIndex(n, index))
  {
    return false;
  }
  i = static_cast<RewriterId>(index);
  return true;
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
  else if (id == PfRule::MACRO_SR_EQ_INTRO)
  {
    // NOTE: technically a macro:
    // (TRANS
    //   (SUBS P1 ... Pn t)
    //   (REWRITE <t.substitute(xn,tn). ... .substitute(x1,t1)>))
    Assert(1 <= args.size() && args.size() <= 2);
    RewriterId idRewriter = RewriterId::REWRITE;
    if (args.size() >= 2)
    {
      if (!getRewriterId(args[1], idRewriter))
      {
        Trace("builtin-pfcheck")
            << "Failed to get id from " << args[1] << std::endl;
        return Node::null();
      }
    }
    Node res = applySubstitutionRewrite(args[0], children, idRewriter);
    return args[0].eqNode(res);
  }
  else if (id == PfRule::MACRO_SR_PRED_INTRO)
  {
    Trace("builtin-pfcheck") << "Check " << id << " " << children.size() << " "
                             << args.size() << std::endl;
    // NOTE: technically a macro:
    // (TRUE_ELIM
    //   (MACRO_SR_EQ_INTRO <children> <args>[0]))
    Assert(1 <= args.size() && args.size() <= 2);
    RewriterId idRewriter = RewriterId::REWRITE;
    if (args.size() >= 2)
    {
      if (!getRewriterId(args[1], idRewriter))
      {
        Trace("builtin-pfcheck")
            << "Failed to get id from " << args[1] << std::endl;
        return Node::null();
      }
    }
    Node res = applySubstitutionRewrite(args[0], children, idRewriter);
    // **** NOTE: can rewrite the witness form here. This enables "symbolic"
    // predicates to check, e.g. (= k t) where k is a purification Skolem for t.
    res = Rewriter::rewrite(res);
    if (!res.isConst() || !res.getConst<bool>())
    {
      Trace("builtin-pfcheck")
          << "Failed to rewrite to true, res=" << res << std::endl;
      return Node::null();
    }
    return args[0];
  }
  else if (id == PfRule::MACRO_SR_PRED_ELIM)
  {
    Trace("builtin-pfcheck") << "Check " << id << " " << children.size() << " "
                             << args.size() << std::endl;
    Assert(children.size() >= 1);
    Assert(args.size() <= 1);
    // NOTE: technically a macro:
    // (TRUE_ELIM
    //   (TRANS
    //     (SYMM (MACRO_SR_EQ_INTRO <children>[1:] F))
    //     (TRUE_INTRO <children>[0])))
    std::vector<Node> exp;
    exp.insert(exp.end(), children.begin() + 1, children.end());
    RewriterId idRewriter = RewriterId::REWRITE;
    if (0<args.size())
    {
      if (!getRewriterId(args[0], idRewriter))
      {
        Trace("builtin-pfcheck")
            << "Failed to get id from " << args[0] << std::endl;
        return Node::null();
      }
    }
    Node res1 = applySubstitutionRewrite(children[0], exp, idRewriter);
    Trace("builtin-pfcheck")
        << "Returned " << res1 << " from " << children[0] << std::endl;
    return res1;
  }
  else if (id == PfRule::MACRO_SR_PRED_TRANSFORM)
  {
    Trace("builtin-pfcheck") << "Check " << id << " " << children.size() << " "
                             << args.size() << std::endl;
    Assert(children.size() >= 1);
    Assert(args.size() <= 2);
    std::vector<Node> exp;
    exp.insert(exp.end(), children.begin() + 1, children.end());
    RewriterId idRewriter = RewriterId::REWRITE;
    if (1<args.size())
    {
      if (!getRewriterId(args[1], idRewriter))
      {
        Trace("builtin-pfcheck")
            << "Failed to get id from " << args[1] << std::endl;
        return Node::null();
      }
    }
    Node res1 = applySubstitutionRewrite(children[0], exp, idRewriter);
    Trace("builtin-pfcheck")
        << "Returned " << res1 << " from " << children[0] << std::endl;
    Node res2 = applySubstitutionRewrite(args[0], exp, idRewriter);
    Trace("builtin-pfcheck")
        << "Returned " << res2 << " from " << args[0] << std::endl;
    // can rewrite the witness forms
    res1 = Rewriter::rewrite(res1);
    res2 = Rewriter::rewrite(res2);
    if (res1!=res2)
    {
      return Node::null();
    }
    return res2;
  }
  // no rule
  return Node::null();
}

}  // namespace builtin
}  // namespace theory
}  // namespace CVC4
