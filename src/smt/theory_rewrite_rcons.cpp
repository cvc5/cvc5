/*********************                                                        */
/*! \file theory_rewrite_rcons.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for reconstructing proofs of THEORY_REWRITE steps.
 **/

#include "smt/theory_rewrite_rcons.h"

#include "expr/proof_checker.h"

namespace CVC4 {
namespace smt {

TheoryRewriteRCons::TheoryRewriteRCons(ProofNodeManager* pnm) : d_pnm(pnm) {}

bool TheoryRewriteRCons::reconstruct(CDProof* cdp,
                                     Node eq,
                                     theory::TheoryId tid,
                                     theory::MethodId mid)
{
  // first, check that maybe its just an evaluation step
  ProofChecker* pc = d_pnm->getChecker();
  Node ceval =
      pc->checkDebug(PfRule::EVALUATE, {}, {eq[0]}, eq, "trewrite-rcons");
  if (!ceval.isNull() && ceval == eq)
  {
    cdp->addStep(eq, PfRule::EVALUATE, {}, {eq[0]});
    return true;
  }

  return false;
}

}  // namespace smt
}  // namespace CVC4
