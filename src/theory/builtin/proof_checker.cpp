/*********************                                                        */
/*! \file proof_checker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of equality proof checker
 **/

#include "theory/builtin/proof_checker.h"

#include "expr/skolem_manager.h"
#include "smt/term_formula_removal.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

const char* toString(MethodId id)
{
  switch (id)
  {
    case MethodId::RW_REWRITE: return "RW_REWRITE";
    case MethodId::RW_IDENTITY: return "RW_IDENTITY";
    case MethodId::SB_DEFAULT: return "SB_DEFAULT";
    case MethodId::SB_LITERAL: return "SB_LITERAL";
    case MethodId::SB_FORMULA: return "SB_FORMULA";
    default: return "MethodId::Unknown";
  };
}

std::ostream& operator<<(std::ostream& out, MethodId id)
{
  out << toString(id);
  return out;
}

Node mkMethodId(MethodId id)
{
  return NodeManager::currentNM()->mkConst(Rational(static_cast<uint32_t>(id)));
}

namespace builtin {

void BuiltinProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::ASSUME, this);
  pc->registerChecker(PfRule::SCOPE, this);
  pc->registerChecker(PfRule::SUBS, this);
  pc->registerChecker(PfRule::REWRITE, this);
  pc->registerChecker(PfRule::MACRO_SR_EQ_INTRO, this);
  pc->registerChecker(PfRule::MACRO_SR_PRED_INTRO, this);
  pc->registerChecker(PfRule::MACRO_SR_PRED_ELIM, this);
  pc->registerChecker(PfRule::MACRO_SR_PRED_TRANSFORM, this);
  pc->registerChecker(PfRule::THEORY_REWRITE, this);
  pc->registerChecker(PfRule::REMOVE_TERM_FORMULA_AXIOM, this);
  // trusted rules
  pc->registerTrustedChecker(PfRule::PREPROCESS, this, 2);
  pc->registerTrustedChecker(PfRule::PREPROCESS_LEMMA, this, 2);
  pc->registerTrustedChecker(PfRule::THEORY_PREPROCESS, this, 2);
  pc->registerTrustedChecker(PfRule::THEORY_PREPROCESS_LEMMA, this, 2);
  pc->registerTrustedChecker(PfRule::WITNESS_AXIOM, this, 2);
}

Node BuiltinProofRuleChecker::applyTheoryRewrite(Node n, bool preRewrite)
{
  TheoryId tid = Theory::theoryOf(n);
  Rewriter* rewriter = Rewriter::getInstance();
  Node nkr = preRewrite ? rewriter->preRewrite(tid, n).d_node
                        : rewriter->postRewrite(tid, n).d_node;
  return nkr;
}


Node BuiltinProofRuleChecker::applySubstitutionRewrite(
    Node n, const std::vector<Node>& exp, MethodId ids, MethodId idr)
{
  Node nks = applySubstitution(n, exp, ids);
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
  else if (idr == MethodId::RW_IDENTITY)
  {
    // does nothing
    return n;
  }
  // unknown rewriter
  Assert(false) << "BuiltinProofRuleChecker::applyRewrite: no rewriter for "
                << idr << std::endl;
  return n;
}

bool BuiltinProofRuleChecker::getSubstitution(Node exp,
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

Node BuiltinProofRuleChecker::applySubstitution(Node n, Node exp, MethodId ids)
{
  TNode var, subs;
  if (!getSubstitution(exp, var, subs, ids))
  {
    return Node::null();
  }
  Trace("builtin-pfcheck-debug")
      << "applySubstitution (" << ids << "): " << var << " -> " << subs
      << " (from " << exp << ")" << std::endl;
  return n.substitute(var, subs);
}

Node BuiltinProofRuleChecker::applySubstitution(Node n,
                                                const std::vector<Node>& exp,
                                                MethodId ids)
{
  Node curr = n;
  // apply substitution one at a time, in reverse order
  for (size_t i = 0, nexp = exp.size(); i < nexp; i++)
  {
    if (exp[nexp - 1 - i].isNull())
    {
      return Node::null();
    }
    curr = applySubstitution(curr, exp[nexp - 1 - i], ids);
    if (curr.isNull())
    {
      break;
    }
  }
  return curr;
}

bool BuiltinProofRuleChecker::getMethodId(TNode n, MethodId& i)
{
  uint32_t index;
  if (!getUInt32(n, index))
  {
    return false;
  }
  i = static_cast<MethodId>(index);
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
      return ant.notNode();
    }
    return NodeManager::currentNM()->mkNode(IMPLIES, ant, children[0]);
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
    Node res = applySubstitution(args[0], exp);
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
    return args[0].eqNode(res);
  }
  else if (id == PfRule::MACRO_SR_EQ_INTRO)
  {
    Assert(1 <= args.size() && args.size() <= 3);
    MethodId ids, idr;
    if (!getMethodIds(args, ids, idr, 1))
    {
      return Node::null();
    }
    Node res = applySubstitutionRewrite(args[0], children, idr);
    return args[0].eqNode(res);
  }
  else if (id == PfRule::MACRO_SR_PRED_INTRO)
  {
    Trace("builtin-pfcheck") << "Check " << id << " " << children.size() << " "
                             << args.size() << std::endl;
    Assert(1 <= args.size() && args.size() <= 3);
    MethodId ids, idr;
    if (!getMethodIds(args, ids, idr, 1))
    {
      return Node::null();
    }
    Node res = applySubstitutionRewrite(args[0], children, ids, idr);
    if (res.isNull())
    {
      return Node::null();
    }
    // **** NOTE: can rewrite the witness form here. This enables certain lemmas
    // to be provable, e.g. (= k t) where k is a purification Skolem for t.
    res = Rewriter::rewrite(SkolemManager::getWitnessForm(res));
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
    Assert(args.size() <= 2);
    std::vector<Node> exp;
    exp.insert(exp.end(), children.begin() + 1, children.end());
    MethodId ids, idr;
    if (!getMethodIds(args, ids, idr, 0))
    {
      return Node::null();
    }
    Node res1 = applySubstitutionRewrite(children[0], exp, ids, idr);
    Trace("builtin-pfcheck") << "Returned " << res1 << std::endl;
    return res1;
  }
  else if (id == PfRule::MACRO_SR_PRED_TRANSFORM)
  {
    Trace("builtin-pfcheck") << "Check " << id << " " << children.size() << " "
                             << args.size() << std::endl;
    Assert(children.size() >= 1);
    Assert(1 <= args.size() && args.size() <= 3);
    Assert(args[0].getType().isBoolean());
    MethodId ids, idr;
    if (!getMethodIds(args, ids, idr, 1))
    {
      return Node::null();
    }
    std::vector<Node> exp;
    exp.insert(exp.end(), children.begin() + 1, children.end());
    Node res1 = applySubstitutionRewrite(children[0], exp, ids, idr);
    Node res2 = applySubstitutionRewrite(args[0], exp, ids, idr);
    // if not already equal, do rewriting
    if (res1 != res2)
    {
      // can rewrite the witness forms
      res1 = Rewriter::rewrite(SkolemManager::getWitnessForm(res1));
      res2 = Rewriter::rewrite(SkolemManager::getWitnessForm(res2));
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
           || id == PfRule::WITNESS_AXIOM)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    return args[0];
  }
  // no rule
  return Node::null();
}

bool BuiltinProofRuleChecker::getMethodIds(const std::vector<Node>& args,
                                           MethodId& ids,
                                           MethodId& idr,
                                           size_t index)
{
  ids = MethodId::SB_DEFAULT;
  idr = MethodId::RW_REWRITE;
  if (args.size() > index)
  {
    if (!getMethodId(args[index], ids))
    {
      Trace("builtin-pfcheck")
          << "Failed to get id from " << args[index] << std::endl;
      return false;
    }
  }
  if (args.size() > index + 1)
  {
    if (!getMethodId(args[index + 1], idr))
    {
      Trace("builtin-pfcheck")
          << "Failed to get id from " << args[index + 1] << std::endl;
      return false;
    }
  }
  return true;
}

void BuiltinProofRuleChecker::addMethodIds(std::vector<Node>& args,
                                           MethodId ids,
                                           MethodId idr)
{
  bool ndefRewriter = (idr != MethodId::RW_REWRITE);
  if (ids != MethodId::SB_DEFAULT || ndefRewriter)
  {
    args.push_back(mkMethodId(ids));
  }
  if (ndefRewriter)
  {
    args.push_back(mkMethodId(idr));
  }
}

}  // namespace builtin
}  // namespace theory
}  // namespace CVC4
