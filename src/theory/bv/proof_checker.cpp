/*********************                                                        */
/*! \file proof_checker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of bit-vectors proof checker
 **/

#include "theory/bv/proof_checker.h"
#include "theory/bv/bv_solver_simple.h"

namespace CVC4 {
namespace theory {
namespace bv {

BVProofRuleChecker::BVProofRuleChecker() : d_bb(new BBSimple(nullptr)) {}

void BVProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::BV_BITBLAST_SIMPLE, this);
}

Node BVProofRuleChecker::checkInternal(PfRule id,
                                       const std::vector<Node>& children,
                                       const std::vector<Node>& args)
{
  if (id == PfRule::BV_BITBLAST_SIMPLE)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    d_bb->bbAtom(args[0]);
    Node bb = d_bb->getStoredBBAtom(args[0]);
    return args[0].eqNode(bb);
  }
  // no rule
  return Node::null();
}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
