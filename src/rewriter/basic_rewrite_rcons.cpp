/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Jörg Schurr, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for basic (non-DSL-dependent) automatic reconstructing proofs of
 * THEORY_REWRITE steps.
 */

#include "rewriter/basic_rewrite_rcons.h"

#include "proof/proof_checker.h"
#include "rewriter/rewrites.h"
#include "smt/env.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

BasicRewriteRCons::BasicRewriteRCons(Env& env) : EnvObj(env) {}

bool BasicRewriteRCons::prove(
    CDProof* cdp, Node a, Node b, theory::TheoryId tid, MethodId mid)
{
  Node eq = a.eqNode(b);
  Trace("trewrite-rcons") << "Reconstruct " << eq << " (from " << tid << ", "
                          << mid << ")" << std::endl;
  Node lhs = eq[0];
  Node rhs = eq[1];
  // this probably should never happen
  if (eq[0] == eq[1])
  {
    Trace("trewrite-rcons") << "...REFL" << std::endl;
    cdp->addStep(eq, ProofRule::REFL, {}, {eq[0]});
    return true;
  }
  // first, check that maybe its just an evaluation step
  if (tryRule(cdp, eq, ProofRule::EVALUATE, {eq[0]}))
  {
    Trace("trewrite-rcons") << "...EVALUATE" << std::endl;
    return true;
  }

  // try theory rewrite (pre-rare)
  ProofRewriteRule prid =
      d_env.getRewriter()->findRule(a, b, theory::TheoryRewriteCtx::PRE_DSL);
  if (prid != ProofRewriteRule::NONE)
  {
    if (tryRule(
            cdp, eq, ProofRule::THEORY_REWRITE, {mkRewriteRuleNode(prid), a}))
    {
      Trace("trewrite-rcons") << "Reconstruct " << eq << " (from " << prid
                              << ", " << mid << ")" << std::endl;
      return true;
    }
  }
  Trace("trewrite-rcons") << "...(fail)" << std::endl;
  return false;
}

bool BasicRewriteRCons::postProve(
    CDProof* cdp, Node a, Node b, theory::TheoryId tid, MethodId mid)
{
  Node eq = a.eqNode(b);

  // try theory rewrite (post-rare)
  ProofRewriteRule prid =
      d_env.getRewriter()->findRule(a, b, theory::TheoryRewriteCtx::POST_DSL);
  if (prid != ProofRewriteRule::NONE)
  {
    if (tryRule(
            cdp, eq, ProofRule::THEORY_REWRITE, {mkRewriteRuleNode(prid), a}))
    {
      Trace("trewrite-rcons") << "Reconstruct (post) " << eq << " (from "
                              << prid << ", " << mid << ")" << std::endl;
      return true;
    }
  }

  Trace("trewrite-rcons") << "...(fail)" << std::endl;
  return false;
}

bool BasicRewriteRCons::tryRule(CDProof* cdp,
                                Node eq,
                                ProofRule r,
                                const std::vector<Node>& args)
{
  Trace("trewrite-rcons-debug") << "Try " << r << std::endl;
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
  // do not provide expected, as this will always succeed if proof checking
  // is disabled
  Node res = pc->checkDebug(r, {}, args, Node::null(), "trewrite-rcons");
  if (!res.isNull() && res == eq)
  {
    cdp->addStep(eq, r, {}, args);
    return true;
  }
  return false;
}

}  // namespace rewriter
}  // namespace cvc5::internal
