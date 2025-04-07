/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Joerg Schurr, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for post-processing proof nodes for DSL rewrite reconstruction.
 */

#include "smt/proof_post_processor_dsl.h"

#include "options/base_options.h"
#include "options/smt_options.h"
#include "proof/proof_ensure_closed.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

ProofPostprocessDsl::ProofPostprocessDsl(Env& env, rewriter::RewriteDb* rdb)
    : EnvObj(env), d_rdbPc(env, rdb)
{
  d_true = nodeManager()->mkConst(true);
  d_tmode = (options().proof.proofGranularityMode
             == options::ProofGranularityMode::DSL_REWRITE_STRICT)
                ? rewriter::TheoryRewriteMode::RESORT
                : rewriter::TheoryRewriteMode::STANDARD;
}

void ProofPostprocessDsl::reconstruct(
    std::vector<std::shared_ptr<ProofNode>>& pfs)
{
  if (pfs.empty())
  {
    return;
  }
  Trace("pp-dsl") << "Reconstruct proofs for " << pfs.size()
                  << " trusted steps..." << std::endl;
  // run an updater for this callback
  ProofNodeUpdater pnu(d_env, *this, false);
  for (std::shared_ptr<ProofNode> p : pfs)
  {
    d_traversing.clear();
    Trace("pp-dsl-process") << "BEGIN update" << std::endl;
    pnu.process(p);
    Trace("pp-dsl-process") << "END update" << std::endl;
    Assert(d_traversing.empty());
  }
}

bool ProofPostprocessDsl::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                       const std::vector<Node>& fa,
                                       bool& continueUpdate)
{
  ProofRule id = pn->getRule();
  continueUpdate = true;
  // we should update if we
  // - Have rule TRUST or TRUST_THEORY_REWRITE,
  // - We have no premises
  // - We are not already recursively expanding >= 3 steps of the above form.
  // We check for the third criteria by tracking a d_traversing vector.
  if ((id == ProofRule::TRUST || id == ProofRule::TRUST_THEORY_REWRITE)
      && pn->getChildren().empty() && d_traversing.size() < 3)
  {
    Trace("pp-dsl-process") << "...push " << pn.get() << std::endl;
    d_traversing.push_back(pn);
    return true;
  }
  return false;
}

bool ProofPostprocessDsl::shouldUpdatePost(std::shared_ptr<ProofNode> pn,
                                           const std::vector<Node>& fa)
{
  // clean up d_traversing at post-traversal
  // note we may have pushed multiple copies of pn consecutively if a proof
  // was updated to another trust step.
  while (!d_traversing.empty() && d_traversing.back() == pn)
  {
    Trace("pp-dsl-process") << "...pop " << pn.get() << std::endl;
    d_traversing.pop_back();
  }
  return false;
}

bool ProofPostprocessDsl::update(Node res,
                                 ProofRule id,
                                 const std::vector<Node>& children,
                                 const std::vector<Node>& args,
                                 CDProof* cdp,
                                 bool& continueUpdate)
{
  continueUpdate = false;
  Assert(id == ProofRule::TRUST || id == ProofRule::TRUST_THEORY_REWRITE);
  Assert(children.empty());
  Assert(!res.isNull());
  bool reqTrueElim = false;
  // if not an equality, make (= res true).
  if (res.getKind() != Kind::EQUAL)
  {
    res = res.eqNode(d_true);
    reqTrueElim = true;
  }
  TheoryId tid = THEORY_LAST;
  MethodId mid = MethodId::RW_REWRITE;
  rewriter::TheoryRewriteMode tm = d_tmode;
  // if theory rewrite, get diagnostic information
  if (id == ProofRule::TRUST_THEORY_REWRITE)
  {
    builtin::BuiltinProofRuleChecker::getTheoryId(args[1], tid);
    getMethodId(args[2], mid);
  }
  else if (id == ProofRule::TRUST)
  {
    TrustId trid;
    getTrustId(args[0], trid);
    if (trid == TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE)
    {
      // If we are MACRO_THEORY_REWRITE_RCONS_SIMPLE, we do not use
      // theory rewrites. This policy ensures that macro theory rewrites are
      // disabled on rewrites which we use for their own reconstruction.
      tm = rewriter::TheoryRewriteMode::NEVER;
    }
  }
  Trace("pp-dsl") << "Prove " << res << " from " << tid << " / " << mid
                  << ", in mode " << tm << std::endl;
  int64_t recLimit = options().proof.proofRewriteRconsRecLimit;
  int64_t stepLimit = options().proof.proofRewriteRconsStepLimit;
  // Attempt to reconstruct the proof of the equality into cdp using the
  // rewrite database proof reconstructor.
  // We record the subgoals in d_subgoals.
  if (d_rdbPc.prove(cdp, res[0], res[1], recLimit, stepLimit, tm))
  {
    // we will update this again, in case the elaboration introduced
    // new trust steps
    continueUpdate = true;
    // If we made (= res true) above, conclude the original res.
    if (reqTrueElim)
    {
      cdp->addStep(res[0], ProofRule::TRUE_ELIM, {res}, {});
      res = res[0];
    }
    Trace("check-dsl") << "Check closed..." << std::endl;
    pfgEnsureClosed(options(), res, cdp, "check-dsl", "check dsl");
    // if successful, we update the proof
    return true;
  }
  // clean up traversing, since we are setting continueUpdate to false
  Assert (!d_traversing.empty());
  Trace("pp-dsl-process") << "...pop due to fail " << d_traversing.back().get() << std::endl;
  d_traversing.pop_back();
  // otherwise no update
  return false;
}

}  // namespace smt
}  // namespace cvc5::internal
