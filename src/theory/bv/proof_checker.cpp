/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of bit-vectors proof checker.
 */

#include "theory/bv/proof_checker.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

void BVProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerTrustedChecker(ProofRule::MACRO_BV_BITBLAST, this, 2);
  pc->registerTrustedChecker(ProofRule::BV_BITBLAST_STEP, this, 2);
  pc->registerChecker(ProofRule::BV_EAGER_ATOM, this);
}

Node BVProofRuleChecker::checkInternal(ProofRule id,
                                       const std::vector<Node>& children,
                                       const std::vector<Node>& args)
{
  if (id == ProofRule::MACRO_BV_BITBLAST)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getKind() == Kind::EQUAL);
    return args[0];
  }
  else if (id == ProofRule::BV_BITBLAST_STEP)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getKind() == Kind::EQUAL);
    return args[0];
  }
  else if (id == ProofRule::BV_EAGER_ATOM)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getKind() == Kind::BITVECTOR_EAGER_ATOM);
    return args[0].eqNode(args[0][0]);
  }
  // no rule
  return Node::null();
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
