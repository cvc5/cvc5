/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of CAD proof checker.
 */

#include "theory/arith/nl/coverings/proof_checker.h"

#include "expr/sequence.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace coverings {

void CoveringsProofRuleChecker::registerTo(ProofChecker* pc)
{
  // trusted rules
  pc->registerTrustedChecker(PfRule::ARITH_NL_COVERING_DIRECT, this, 2);
  pc->registerTrustedChecker(PfRule::ARITH_NL_COVERING_RECURSIVE, this, 2);
}

Node CoveringsProofRuleChecker::checkInternal(PfRule id,
                                        const std::vector<Node>& children,
                                        const std::vector<Node>& args)
{
  Trace("nl-cov-checker") << "Checking " << id << std::endl;
  for (const auto& c : children)
  {
    Trace("nl-cov-checker") << "\t" << c << std::endl;
  }
  if (id == PfRule::ARITH_NL_COVERING_DIRECT)
  {
    Assert(args.size() == 1);
    return args[0];
  }
  if (id == PfRule::ARITH_NL_COVERING_RECURSIVE)
  {
    Assert(args.size() == 1);
    return args[0];
  }
  return Node::null();
}

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
