/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of equality proof checker.
 */

#include "theory/builtin/proof_checker.h"

#include "expr/skolem_manager.h"
#include "smt/term_formula_removal.h"
#include "theory/evaluator.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/theory.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace builtin {

void BuiltinProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::ASSUME, this);
  pc->registerChecker(PfRule::SCOPE, this);
  pc->registerChecker(PfRule::SUBS, this);
  pc->registerChecker(PfRule::REWRITE, this);
  pc->registerChecker(PfRule::EVALUATE, this);
  pc->registerChecker(PfRule::MACRO_SR_EQ_INTRO, this);
  pc->registerChecker(PfRule::MACRO_SR_PRED_INTRO, this);
  pc->registerChecker(PfRule::MACRO_SR_PRED_ELIM, this);
  pc->registerChecker(PfRule::MACRO_SR_PRED_TRANSFORM, this);
  pc->registerChecker(PfRule::THEORY_REWRITE, this);
  pc->registerChecker(PfRule::REMOVE_TERM_FORMULA_AXIOM, this);
  // trusted rules
  pc->registerTrustedChecker(PfRule::THEORY_LEMMA, this, 1);
  pc->registerTrustedChecker(PfRule::PREPROCESS, this, 3);
  pc->registerTrustedChecker(PfRule::PREPROCESS_LEMMA, this, 3);
  pc->registerTrustedChecker(PfRule::THEORY_PREPROCESS, this, 3);
  pc->registerTrustedChecker(PfRule::THEORY_PREPROCESS_LEMMA, this, 3);
  pc->registerTrustedChecker(PfRule::THEORY_EXPAND_DEF, this, 3);
  pc->registerTrustedChecker(PfRule::WITNESS_AXIOM, this, 3);
  pc->registerTrustedChecker(PfRule::TRUST_REWRITE, this, 1);
  pc->registerTrustedChecker(PfRule::TRUST_SUBS, this, 1);
  pc->registerTrustedChecker(PfRule::TRUST_SUBS_MAP, this, 1);
  pc->registerTrustedChecker(PfRule::TRUST_SUBS_EQ, this, 3);
  pc->registerTrustedChecker(PfRule::THEORY_INFERENCE, this, 3);
}

Node BuiltinProofRuleChecker::applySubstitutionRewrite(
    Node n,
    const std::vector<Node>& exp,
    MethodId ids,
    MethodId ida,
    MethodId idr)
{
  Node nks = applySubstitution(n, exp, ids, ida);
  return applyRewrite(nks, idr);
}

Node BuiltinProofRuleChecker::applyRewrite(Node n, MethodId idr)
{
  Trace("builtin-pfcheck-debug")
      << "applyRewrite (" << idr << "): " << n << std::endl;
  if (idr == MethodId::RW_REWRITE)
  {
    return Rewriter::rewrite(n);
  }
  if (idr == MethodId::RW_EXT_REWRITE)
  {
    return d_ext_rewriter.extendedRewrite(n);
  }
  if (idr == MethodId::RW_REWRITE_EQ_EXT)
  {
    return Rewriter::rewriteEqualityExt(n);
  }
  if (idr == MethodId::RW_EVALUATE)
  {
    Evaluator eval;
    return eval.eval(n, {}, {}, false);
  }
  if (idr == MethodId::RW_IDENTITY)
  {
    // does nothing
    return n;
  }
  // unknown rewriter
  Assert(false) << "BuiltinProofRuleChecker::applyRewrite: no rewriter for "
                << idr << std::endl;
  return n;
}

bool BuiltinProofRuleChecker::getSubstitutionForLit(Node exp,
                                                    TNode& var,
                                                    TNode& subs,
                                                    MethodId ids)
{
  if (ids == MethodId::SB_DEFAULT)
  {
    if (exp.getKind() != EQUAL)
    {
      return false;
    }
    var = exp[0];
    subs = exp[1];
  }
  else if (ids == MethodId::SB_LITERAL)
  {
    bool polarity = exp.getKind() != NOT;
    var = polarity ? exp : exp[0];
    subs = NodeManager::currentNM()->mkConst(polarity);
  }
  else if (ids == MethodId::SB_FORMULA)
  {
    var = exp;
    subs = NodeManager::currentNM()->mkConst(true);
  }
  else
  {
    Assert(false) << "BuiltinProofRuleChecker::applySubstitution: no "
                     "substitution for "
                  << ids << std::endl;
    return false;
  }
  return true;
}

bool BuiltinProofRuleChecker::getSubstitutionFor(Node exp,
                                                 std::vector<TNode>& vars,
                                                 std::vector<TNode>& subs,
                                                 std::vector<TNode>& from,
                                                 MethodId ids)
{
  TNode v;
  TNode s;
  if (exp.getKind() == AND && ids == MethodId::SB_DEFAULT)
  {
    for (const Node& ec : exp)
    {
      // non-recursive, do not use nested AND
      if (!getSubstitutionForLit(ec, v, s, ids))
      {
        return false;
      }
      vars.push_back(v);
      subs.push_back(s);
      from.push_back(ec);
    }
    return true;
  }
  bool ret = getSubstitutionForLit(exp, v, s, ids);
  vars.push_back(v);
  subs.push_back(s);
  from.push_back(exp);
  return ret;
}

Node BuiltinProofRuleChecker::applySubstitution(Node n,
                                                Node exp,
                                                MethodId ids,
                                                MethodId ida)
{
  std::vector<Node> expv{exp};
  return applySubstitution(n, expv, ids, ida);
}

Node BuiltinProofRuleChecker::applySubstitution(Node n,
                                                const std::vector<Node>& exp,
                                                MethodId ids,
                                                MethodId ida)
{
  std::vector<TNode> vars;
  std::vector<TNode> subs;
  std::vector<TNode> from;
  for (size_t i = 0, nexp = exp.size(); i < nexp; i++)
  {
    if (exp[i].isNull())
    {
      return Node::null();
    }
    if (!getSubstitutionFor(exp[i], vars, subs, from, ids))
    {
      return Node::null();
    }
  }
  if (ida == MethodId::SBA_SIMUL)
  {
    // simply apply the simultaneous substitution now
    return n.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
  }
  else if (ida == MethodId::SBA_FIXPOINT)
  {
    SubstitutionMap sm;
    for (size_t i = 0, nvars = vars.size(); i < nvars; i++)
    {
      sm.addSubstitution(vars[i], subs[i]);
    }
    Node ns = sm.apply(n);
    return ns;
  }
  Assert(ida == MethodId::SBA_SEQUENTIAL);
  // we prefer n traversals of the term to n^2/2 traversals of range terms
  Node ns = n;
  for (size_t i = 0, nvars = vars.size(); i < nvars; i++)
  {
    TNode v = vars[(nvars - 1) - i];
    TNode s = subs[(nvars - 1) - i];
    ns = ns.substitute(v, s);
  }
  return ns;
}

Node BuiltinProofRuleChecker::checkInternal(PfRule id,
                                            const std::vector<Node>& children,
                                            const std::vector<Node>& args)
{
  NodeManager * nm = NodeManager::currentNM();
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
    Node ant = nm->mkAnd(args);
    // if the conclusion is false, its the negated antencedant only
    if (children[0].isConst() && !children[0].getConst<bool>())
    {
      return ant.notNode();
    }
    return nm->mkNode(IMPLIES, ant, children[0]);
  }
  else if (id == PfRule::SUBS)
  {
    Assert(children.size() > 0);
    Assert(1 <= args.size() && args.size() <= 2);
    MethodId ids = MethodId::SB_DEFAULT;
    if (args.size() == 2 && !getMethodId(args[1], ids))
    {
      return Node::null();
    }
    std::vector<Node> exp;
    for (size_t i = 0, nchild = children.size(); i < nchild; i++)
    {
      exp.push_back(children[i]);
    }
    Node res = applySubstitution(args[0], exp, ids);
    if (res.isNull())
    {
      return Node::null();
    }
    return args[0].eqNode(res);
  }
  else if (id == PfRule::REWRITE)
  {
    Assert(children.empty());
    Assert(1 <= args.size() && args.size() <= 2);
    MethodId idr = MethodId::RW_REWRITE;
    if (args.size() == 2 && !getMethodId(args[1], idr))
    {
      return Node::null();
    }
    Node res = applyRewrite(args[0], idr);
    if (res.isNull())
    {
      return Node::null();
    }
    return args[0].eqNode(res);
  }
  else if (id == PfRule::EVALUATE)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node res = applyRewrite(args[0], MethodId::RW_EVALUATE);
    if (res.isNull())
    {
      return Node::null();
    }
    return args[0].eqNode(res);
  }
  else if (id == PfRule::MACRO_SR_EQ_INTRO)
  {
    Assert(1 <= args.size() && args.size() <= 4);
    MethodId ids, ida, idr;
    if (!getMethodIds(args, ids, ida, idr, 1))
    {
      return Node::null();
    }
    Node res = applySubstitutionRewrite(args[0], children, ids, ida, idr);
    if (res.isNull())
    {
      return Node::null();
    }
    return args[0].eqNode(res);
  }
  else if (id == PfRule::MACRO_SR_PRED_INTRO)
  {
    Trace("builtin-pfcheck") << "Check " << id << " " << children.size() << " "
                             << args[0] << std::endl;
    Assert(1 <= args.size() && args.size() <= 4);
    MethodId ids, ida, idr;
    if (!getMethodIds(args, ids, ida, idr, 1))
    {
      return Node::null();
    }
    Node res = applySubstitutionRewrite(args[0], children, ids, ida, idr);
    if (res.isNull())
    {
      return Node::null();
    }
    Trace("builtin-pfcheck") << "Result is " << res << std::endl;
    Trace("builtin-pfcheck") << "Witness form is "
                             << SkolemManager::getOriginalForm(res) << std::endl;
    // **** NOTE: can rewrite the witness form here. This enables certain lemmas
    // to be provable, e.g. (= k t) where k is a purification Skolem for t.
    res = Rewriter::rewrite(SkolemManager::getOriginalForm(res));
    if (!res.isConst() || !res.getConst<bool>())
    {
      Trace("builtin-pfcheck")
          << "Failed to rewrite to true, res=" << res << std::endl;
      return Node::null();
    }
    Trace("builtin-pfcheck") << "...success" << std::endl;
    return args[0];
  }
  else if (id == PfRule::MACRO_SR_PRED_ELIM)
  {
    Trace("builtin-pfcheck") << "Check " << id << " " << children.size() << " "
                             << args.size() << std::endl;
    Assert(children.size() >= 1);
    Assert(args.size() <= 3);
    std::vector<Node> exp;
    exp.insert(exp.end(), children.begin() + 1, children.end());
    MethodId ids, ida, idr;
    if (!getMethodIds(args, ids, ida, idr, 0))
    {
      return Node::null();
    }
    Node res1 = applySubstitutionRewrite(children[0], exp, ids, ida, idr);
    Trace("builtin-pfcheck") << "Returned " << res1 << std::endl;
    return res1;
  }
  else if (id == PfRule::MACRO_SR_PRED_TRANSFORM)
  {
    Trace("builtin-pfcheck") << "Check " << id << " " << children.size() << " "
                             << args.size() << std::endl;
    Assert(children.size() >= 1);
    Assert(1 <= args.size() && args.size() <= 4);
    Assert(args[0].getType().isBoolean());
    MethodId ids, ida, idr;
    if (!getMethodIds(args, ids, ida, idr, 1))
    {
      return Node::null();
    }
    std::vector<Node> exp;
    exp.insert(exp.end(), children.begin() + 1, children.end());
    Node res1 = applySubstitutionRewrite(children[0], exp, ids, ida, idr);
    Node res2 = applySubstitutionRewrite(args[0], exp, ids, ida, idr);
    // if not already equal, do rewriting
    if (res1 != res2)
    {
      // can rewrite the witness forms
      res1 = Rewriter::rewrite(SkolemManager::getOriginalForm(res1));
      res2 = Rewriter::rewrite(SkolemManager::getOriginalForm(res2));
      if (res1.isNull() || res1 != res2)
      {
        Trace("builtin-pfcheck") << "Failed to match results" << std::endl;
        Trace("builtin-pfcheck-debug") << res1 << " vs " << res2 << std::endl;
        return Node::null();
      }
    }
    return args[0];
  }
  else if (id == PfRule::REMOVE_TERM_FORMULA_AXIOM)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    return RemoveTermFormulas::getAxiomFor(args[0]);
  }
  else if (id == PfRule::PREPROCESS || id == PfRule::PREPROCESS_LEMMA
           || id == PfRule::THEORY_PREPROCESS
           || id == PfRule::THEORY_PREPROCESS_LEMMA
           || id == PfRule::THEORY_EXPAND_DEF || id == PfRule::WITNESS_AXIOM
           || id == PfRule::THEORY_LEMMA || id == PfRule::THEORY_REWRITE
           || id == PfRule::TRUST_REWRITE || id == PfRule::TRUST_SUBS
           || id == PfRule::TRUST_SUBS_MAP || id == PfRule::TRUST_SUBS_EQ
           || id == PfRule::THEORY_INFERENCE)
  {
    // "trusted" rules
    Assert(!args.empty());
    Assert(args[0].getType().isBoolean());
    return args[0];
  }

  // no rule
  return Node::null();
}

bool BuiltinProofRuleChecker::getTheoryId(TNode n, TheoryId& tid)
{
  uint32_t i;
  if (!getUInt32(n, i))
  {
    return false;
  }
  tid = static_cast<TheoryId>(i);
  return true;
}

Node BuiltinProofRuleChecker::mkTheoryIdNode(TheoryId tid)
{
  return NodeManager::currentNM()->mkConst(
      Rational(static_cast<uint32_t>(tid)));
}

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5
