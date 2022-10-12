/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finite fields theory
 */

#include "theory/ff/theory_ff.h"

#include <cerrno>
#include <fstream>
#include <iostream>
#include <numeric>
#include <sstream>
#include <unordered_map>

#include "expr/node_manager_attributes.h"
#include "expr/node_traversal.h"
#include "options/ff_options.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"
#include "util/statistics_registry.h"
#include "util/utility.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace ff {

void noCoCoA()
{
  throw LogicException(
      "cvc5 can't solve field problems since it was not configured with "
      "--cocoa");
}

TheoryFiniteFields::TheoryFiniteFields(Env& env,
                                       OutputChannel& out,
                                       Valuation valuation)
    : Theory(THEORY_FF, env, out, valuation),
      d_state(env, valuation),
      d_im(env, *this, d_state, getStatsPrefix(THEORY_FF)),
      d_eqNotify(d_im),
      d_stats(
          std::make_unique<FfStatistics>(statisticsRegistry(), "theory::ff::"))
{
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheoryFiniteFields::~TheoryFiniteFields() {}

TheoryRewriter* TheoryFiniteFields::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryFiniteFields::getProofChecker() { return nullptr; }

bool TheoryFiniteFields::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_eqNotify;
  esi.d_name = "theory::ff::ee";
  return true;
}

void TheoryFiniteFields::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  d_equalityEngine->addFunctionKind(Kind::FINITE_FIELD_MULT);
  d_equalityEngine->addFunctionKind(Kind::FINITE_FIELD_NEG);
  d_equalityEngine->addFunctionKind(Kind::FINITE_FIELD_ADD);
}

void TheoryFiniteFields::postCheck(Effort level)
{
#ifdef CVC5_USE_COCOA
  Trace("ff::check") << "ff::check : " << level << std::endl;
  for (auto& subTheory : d_subTheories)
  {
    subTheory.second.postCheck(level);
    if (subTheory.second.inConflict())
    {
      d_im.conflict(
          NodeManager::currentNM()->mkAnd(subTheory.second.conflict()),
          InferenceId::ARITH_FF);
    }
  }
#else  /* CVC5_USE_COCOA */
  noCoCoA();
#endif /* CVC5_USE_COCOA */
}

void TheoryFiniteFields::notifyFact(TNode atom,
                                    bool polarity,
                                    TNode fact,
                                    bool isInternal)
{
#ifdef CVC5_USE_COCOA
  Trace("ff::check") << "ff::notifyFact : " << fact << " @ level "
                     << context()->getLevel() << std::endl;
  d_subTheories.at(atom[0].getType()).notifyFact(fact);
#else  /* CVC5_USE_COCOA */
  noCoCoA();
#endif /* CVC5_USE_COCOA */
}

bool TheoryFiniteFields::collectModelValues(TheoryModel* m,
                                            const std::set<Node>& termSet)
{
#ifdef CVC5_USE_COCOA
  Trace("ff::model") << "Term set: " << termSet << std::endl;
  for (const auto& subTheory : d_subTheories)
  {
    for (const auto& entry : subTheory.second.model())
    {
      Trace("ff::model") << "Model entry: " << entry.first << " -> "
                         << entry.second << std::endl;
      if (termSet.count(entry.first))
      {
        bool okay = m->assertEquality(entry.first, entry.second, true);
        Assert(okay) << "Our model was rejected";
      }
    }
  }
#else  /* CVC5_USE_COCOA */
  noCoCoA();
#endif /* CVC5_USE_COCOA */
  return true;
}

void TheoryFiniteFields::computeCareGraph()
{
  // TODO
}

TrustNode TheoryFiniteFields::explain(TNode node)
{
  // TODO
  return TrustNode::null();
}

Node TheoryFiniteFields::getModelValue(TNode node)
{
  // TODO
  return Node::null();
}

void TheoryFiniteFields::preRegisterTerm(TNode node)
{
#ifdef CVC5_USE_COCOA
  Trace("ff::register") << "ff::preRegisterTerm : " << node << std::endl;
  TypeNode ty = node.getType();
  TypeNode fieldTy = ty;
  if (!ty.isFiniteField())
  {
    Assert(node.getKind() == Kind::EQUAL);
    fieldTy = node[0].getType();
  }
  if (d_subTheories.count(fieldTy) == 0)
  {
    d_subTheories.try_emplace(
        fieldTy, d_env, d_stats.get(), ty.getFfSize());
  }
  d_subTheories.at(fieldTy).preRegisterTerm(node);
#else  /* CVC5_USE_COCOA */
  noCoCoA();
#endif /* CVC5_USE_COCOA */
}

TrustNode TheoryFiniteFields::ppRewrite(TNode n, std::vector<SkolemLemma>& lems)
{
  // TODO
  return TrustNode::null();
}

Theory::PPAssertStatus TheoryFiniteFields::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  TNode in = tin.getNode();
  Trace("ff::pp") << "ff::ppAssert : " << in << std::endl;
  Theory::PPAssertStatus status = Theory::PP_ASSERT_STATUS_UNSOLVED;
  return status;
}

void TheoryFiniteFields::presolve()
{
  // TODO
}

bool TheoryFiniteFields::isEntailed(Node n, bool pol)
{
  // TODO
  return false;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
