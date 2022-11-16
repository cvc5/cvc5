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

#include "expr/node_traversal.h"
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
      d_eqNotify(d_im)
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
  // TODO
}

void TheoryFiniteFields::notifyFact(TNode atom,
                                    bool polarity,
                                    TNode fact,
                                    bool isInternal)
{
  // TODO
}

bool TheoryFiniteFields::collectModelValues(TheoryModel* m,
                                            const std::set<Node>& termSet)
{
  // TODO
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
  // TODO
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
