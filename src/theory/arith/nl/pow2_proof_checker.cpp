/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the Pow2 proof checker.
 */

#include "theory/arith/nl/pow2_proof_checker.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

Pow2ProofRuleChecker::Pow2ProofRuleChecker(NodeManager* nm)
    : ProofRuleChecker(nm)
{
}

void Pow2ProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(ProofRule::ARITH_POW2_INIT, this);
  pc->registerChecker(ProofRule::ARITH_POW2_MONOTONE, this);
  pc->registerChecker(ProofRule::ARITH_POW2_DIV0, this);
  pc->registerChecker(ProofRule::ARITH_POW2_LOWER_BOUND, this);
}

Node Pow2ProofRuleChecker::checkInternal(
    ProofRule id,
    [[maybe_unused]] const std::vector<Node>& children,
    [[maybe_unused]] const std::vector<Node>& args)
{
  switch (id)
  {
    case ProofRule::ARITH_POW2_INIT:
    case ProofRule::ARITH_POW2_MONOTONE:
    case ProofRule::ARITH_POW2_DIV0:
    case ProofRule::ARITH_POW2_LOWER_BOUND:
    default: return Node::null();
  }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
