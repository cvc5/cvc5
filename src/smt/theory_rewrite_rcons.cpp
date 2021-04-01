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

using namespace cvc5::kind;

namespace cvc5 {
namespace smt {

TheoryRewriteRCons::TheoryRewriteRCons(ProofNodeManager* pnm) : d_pnm(pnm) {}

bool TheoryRewriteRCons::reconstruct(CDProof* cdp,
                                     Node eq,
                                     theory::TheoryId tid,
                                     theory::MethodId mid)
{
  Assert(eq.getKind() == EQUAL);
  Trace("trewrite-rcons") << "Reconstruct " << eq << " (from " << tid << ", "
                          << mid << ")" << std::endl;
  Node lhs = eq[0];
  Node rhs = eq[1];
  // this probably should never happen
  if (eq[0] == eq[1])
  {
    Trace("trewrite-rcons") << "...REFL" << std::endl;
    cdp->addStep(eq, PfRule::REFL, {}, {eq[0]});
    return true;
  }
  // first, check that maybe its just an evaluation step
  if (tryRule(cdp, eq, PfRule::EVALUATE, {eq[0]}))
  {
    Trace("trewrite-rcons") << "...EVALUATE" << std::endl;
    return true;
  }

  return false;
}

bool TheoryRewriteRCons::tryRule(CDProof* cdp,
                                 Node eq,
                                 PfRule r,
                                 const std::vector<Node>& args)
{
  ProofChecker* pc = d_pnm->getChecker();
  Node res = pc->checkDebug(r, {}, args, eq, "trewrite-rcons");
  if (!res.isNull() && res == eq)
  {
    cdp->addStep(eq, r, {}, args);
    return true;
  }
  return false;
}

}  // namespace smt
}  // namespace cvc5
