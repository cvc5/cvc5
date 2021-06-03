/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory of booleans.
 */

#include "theory/booleans/theory_bool.h"

#include <stack>
#include <vector>

#include "proof/proof_node_manager.h"
#include "smt_util/boolean_simplification.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/booleans/theory_bool_rewriter.h"
#include "theory/substitutions.h"
#include "theory/theory.h"
#include "theory/trust_substitutions.h"
#include "theory/valuation.h"
#include "util/hash.h"

namespace cvc5 {
namespace theory {
namespace booleans {

TheoryBool::TheoryBool(context::Context* c,
                       context::UserContext* u,
                       OutputChannel& out,
                       Valuation valuation,
                       const LogicInfo& logicInfo,
                       ProofNodeManager* pnm)
    : Theory(THEORY_BOOL, c, u, out, valuation, logicInfo, pnm)
{
}

Theory::PPAssertStatus TheoryBool::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  TNode in = tin.getNode();
  if (in.getKind() == kind::CONST_BOOLEAN && !in.getConst<bool>()) {
    // If we get a false literal, we're in conflict
    return PP_ASSERT_STATUS_CONFLICT;
  }

  // Add the substitution from the variable to its value
  if (in.getKind() == kind::NOT) {
    if (in[0].isVar())
    {
      outSubstitutions.addSubstitutionSolved(
          in[0], NodeManager::currentNM()->mkConst<bool>(false), tin);
      return PP_ASSERT_STATUS_SOLVED;
    }
  } else {
    if (in.isVar())
    {
      outSubstitutions.addSubstitutionSolved(
          in, NodeManager::currentNM()->mkConst<bool>(true), tin);
      return PP_ASSERT_STATUS_SOLVED;
    }
  }

  return Theory::ppAssert(tin, outSubstitutions);
}

TheoryRewriter* TheoryBool::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryBool::getProofChecker() { return &d_checker; }

std::string TheoryBool::identify() const { return std::string("TheoryBool"); }

}  // namespace booleans
}  // namespace theory
}  // namespace cvc5
