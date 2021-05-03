/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of CAD proof checker.
 */

#include "theory/arith/nl/cad/proof_checker.h"

#include "expr/sequence.h"
#include "theory/rewriter.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

void CADProofRuleChecker::registerTo(ProofChecker* pc)
{
  // trusted rules
  pc->registerTrustedChecker(PfRule::ARITH_NL_CAD_DIRECT, this, 2);
  pc->registerTrustedChecker(PfRule::ARITH_NL_CAD_RECURSIVE, this, 2);
}

Node CADProofRuleChecker::checkInternal(PfRule id,
                                        const std::vector<Node>& children,
                                        const std::vector<Node>& args)
{
  Trace("nl-cad-checker") << "Checking " << id << std::endl;
  for (const auto& c : children)
  {
    Trace("nl-cad-checker") << "\t" << c << std::endl;
  }
  if (id == PfRule::ARITH_NL_CAD_DIRECT)
  {
    Assert(args.size() == 1);
    return args[0];
  }
  if (id == PfRule::ARITH_NL_CAD_RECURSIVE)
  {
    Assert(args.size() == 1);
    return args[0];
  }
  return Node::null();
}

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
