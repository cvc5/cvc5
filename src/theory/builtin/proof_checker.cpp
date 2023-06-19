/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of equality proof checker.
 */

#include "theory/builtin/proof_checker.h"

#include "expr/skolem_manager.h"
#include "rewriter/rewrite_db.h"
#include "rewriter/rewrite_db_term_process.h"
#include "rewriter/rewrite_proof_rule.h"
#include "smt/env.h"
#include "smt/term_formula_removal.h"
#include "theory/evaluator.h"
#include "theory/quantifiers/extended_rewrite.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/theory.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace builtin {

BuiltinProofRuleChecker::BuiltinProofRuleChecker(Env& env)
    : d_env(env), d_rdb(nullptr)
{
}

void BuiltinProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::ASSUME, this);
  pc->registerChecker(PfRule::SCOPE, this);
  pc->registerChecker(PfRule::SUBS, this);
  pc->registerChecker(PfRule::EVALUATE, this);
  pc->registerChecker(PfRule::ANNOTATION, this);
  pc->registerChecker(PfRule::REMOVE_TERM_FORMULA_AXIOM, this);
  pc->registerChecker(PfRule::ENCODE_PRED_TRANSFORM, this);
  pc->registerChecker(PfRule::DSL_REWRITE, this);
  // rules depending on the rewriter
  pc->registerTrustedChecker(PfRule::REWRITE, this, 4);
  pc->registerTrustedChecker(PfRule::MACRO_SR_EQ_INTRO, this, 4);
  pc->registerTrustedChecker(PfRule::MACRO_SR_PRED_INTRO, this, 4);
  pc->registerTrustedChecker(PfRule::MACRO_SR_PRED_ELIM, this, 4);
  pc->registerTrustedChecker(PfRule::MACRO_SR_PRED_TRANSFORM, this, 4);
  pc->registerTrustedChecker(PfRule::THEORY_REWRITE, this, 4);
  // trusted rules
  pc->registerTrustedChecker(PfRule::THEORY_LEMMA, this, 1);
  pc->registerTrustedChecker(PfRule::PREPROCESS, this, 3);
  pc->registerTrustedChecker(PfRule::PREPROCESS_LEMMA, this, 3);
  pc->registerTrustedChecker(PfRule::THEORY_PREPROCESS, this, 3);
  pc->registerTrustedChecker(PfRule::THEORY_PREPROCESS_LEMMA, this, 3);
  pc->registerTrustedChecker(PfRule::THEORY_EXPAND_DEF, this, 3);
  pc->registerTrustedChecker(PfRule::WITNESS_AXIOM, this, 3);
  pc->registerTrustedChecker(PfRule::TRUST_REWRITE, this, 1);
  pc->registerTrustedChecker(PfRule::TRUST_FLATTENING_REWRITE, this, 1);
  pc->registerTrustedChecker(PfRule::TRUST_SUBS, this, 1);
  pc->registerTrustedChecker(PfRule::TRUST_SUBS_MAP, this, 1);
  pc->registerTrustedChecker(PfRule::TRUST_SUBS_EQ, this, 3);
  pc->registerTrustedChecker(PfRule::THEORY_INFERENCE, this, 3);
  // external proof rules
  pc->registerChecker(PfRule::LFSC_RULE, this);
  pc->registerChecker(PfRule::ALETHE_RULE, this);

  d_rdb = pc->getRewriteDatabase();
}

Node BuiltinProofRuleChecker::applySubstitutionRewrite(
    Node n,
    const std::vector<Node>& exp,
    MethodId ids,
    MethodId ida,
    MethodId idr)
{
  Node nks = applySubstitution(n, exp, ids, ida);
  return d_env.rewriteViaMethod(nks, idr);
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
    Assert(1 <= args.size() && args.size() <= 3) << "Args: " << args;
    MethodId ids = MethodId::SB_DEFAULT;
    if (args.size() >= 2 && !getMethodId(args[1], ids))
    {
      return Node::null();
    }
    MethodId ida = MethodId::SBA_SEQUENTIAL;
    if (args.size() >= 3 && !getMethodId(args[2], ida))
    {
      return Node::null();
    }
    std::vector<Node> exp;
    for (size_t i = 0, nchild = children.size(); i < nchild; i++)
    {
      exp.push_back(children[i]);
    }
    Node res = applySubstitution(args[0], exp, ids, ida);
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
    Node res = d_env.rewriteViaMethod(args[0], idr);
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
    Node res = d_env.rewriteViaMethod(args[0], MethodId::RW_EVALUATE);
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
    res = d_env.getRewriter()->rewrite(SkolemManager::getOriginalForm(res));
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
      Trace("builtin-pfcheck-debug")
          << "Failed to show " << res1 << " == " << res2
          << ", resort to original forms..." << std::endl;
      // can rewrite the witness forms
      res1 = d_env.getRewriter()->rewrite(SkolemManager::getOriginalForm(res1));
      res2 = d_env.getRewriter()->rewrite(SkolemManager::getOriginalForm(res2));
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
           || id == PfRule::TRUST_FLATTENING_REWRITE
           || id == PfRule::TRUST_REWRITE || id == PfRule::TRUST_SUBS
           || id == PfRule::TRUST_SUBS_MAP || id == PfRule::TRUST_SUBS_EQ
           || id == PfRule::THEORY_INFERENCE)
  {
    // "trusted" rules
    Assert(!args.empty());
    Assert(args[0].getType().isBoolean());
    return args[0];
  }
  else if (id == PfRule::LFSC_RULE || id == PfRule::ALETHE_RULE)
  {
    Assert(args.size() > 1);
    Assert(args[0].getType().isInteger());
    return args[1];
  }
  else if (id == PfRule::ENCODE_PRED_TRANSFORM)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    rewriter::RewriteDbNodeConverter rconv;
    Node f = children[0];
    Node g = args[0];
    // equivalent up to conversion via utility
    if (rconv.convert(f) != rconv.convert(g))
    {
      return Node::null();
    }
    return g;
  }
  else if (id == PfRule::ANNOTATION)
  {
    Assert(children.size() == 1);
    return children[0];
  }
  else if (id == PfRule::DSL_REWRITE)
  {
    // consult rewrite db, apply args[1]...args[n] as a substituion
    // to variable list and prove equality between LHS and RHS.
    Assert(d_rdb != nullptr);
    rewriter::DslPfRule di;
    if (!getDslPfRule(args[0], di))
    {
      return Node::null();
    }
    const rewriter::RewriteProofRule& rpr = d_rdb->getRule(di);
    const std::vector<Node>& varList = rpr.getVarList();
    const std::vector<Node>& conds = rpr.getConditions();
    std::vector<Node> subs(args.begin() + 1, args.end());
    if (varList.size() != subs.size())
    {
      return Node::null();
    }
    // check whether child proof match
    if (conds.size() != children.size())
    {
      return Node::null();
    }
    for (size_t i = 0, nchildren = children.size(); i < nchildren; i++)
    {
      Node scond = expr::narySubstitute(conds[i], varList, subs);
      if (scond != children[i])
      {
        return Node::null();
      }
    }
    return rpr.getConclusionFor(subs);
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
  return NodeManager::currentNM()->mkConstInt(
      Rational(static_cast<uint32_t>(tid)));
}

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5::internal
