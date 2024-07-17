/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
  d_true = NodeManager::currentNM()->mkConst(true);
  d_tmode = (options().proof.proofGranularityMode
             == options::ProofGranularityMode::DSL_REWRITE_STRICT)
                ? rewriter::TheoryRewriteMode::RESORT
                : rewriter::TheoryRewriteMode::STANDARD;
}

void ProofPostprocessDsl::reconstruct(
    std::unordered_set<std::shared_ptr<ProofNode>>& pfs)
{
  Trace("pp-dsl") << "Reconstruct proofs for " << pfs.size()
                  << " trusted steps..." << std::endl;
  // run an updater for this callback
  ProofNodeUpdater pnu(d_env, *this, false);
  for (std::shared_ptr<ProofNode> p : pfs)
  {
    pnu.process(p);
  }
  // We run until subgoals are empty. Note that this loop is only expected
  // to run once, and moreover is guaranteed to run only once if the only
  // trusted steps added have id MACRO_THEORY_REWRITE_RCONS_SIMPLE. However,
  // in rare cases, an elaboration may require adding a trust step that itself
  // expects to require theory rewrites to prove (MACRO_THEORY_REWRITE_RCONS)
  // in which case this loop may run twice. We manually limit this loop to
  // run no more than 2 times.
  size_t iter = 0;
  while (!d_subgoals.empty())
  {
    iter++;
    if (iter >= 3)
    {
      // prevent any accidental infinite loops
      break;
    }
    std::vector<std::shared_ptr<ProofNode>> sgs = d_subgoals;
    Trace("pp-dsl") << "Also reconstruct proofs for " << sgs.size()
                    << " subgoals..." << std::endl;
    d_subgoals.clear();
    // Do not use theory rewrites to fill in remaining subgoals. This prevents
    // generating subgoals in proofs of subgoals.
    rewriter::TheoryRewriteMode mprev = d_tmode;
    TrustId tid;
    for (std::shared_ptr<ProofNode> p : sgs)
    {
      // determine if we should disable theory rewrites, this is the case if the
      // trust id is MACRO_THEORY_REWRITE_RCONS_SIMPLE.
      d_tmode = mprev;
      if (p->getRule() == ProofRule::TRUST)
      {
        getTrustId(p->getArguments()[0], tid);
        if (tid == TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE)
        {
          d_tmode = rewriter::TheoryRewriteMode::NEVER;
        }
      }
      pnu.process(p);
    }
    d_tmode = mprev;
  }
  // should never construct a subgoal for a step from a subgoal
  if (!d_subgoals.empty())
  {
    Trace("pp-dsl") << "REM SUBGOALS: " << std::endl;
    for (std::shared_ptr<ProofNode> p : d_subgoals)
    {
      Warning() << "WARNING: unproven subgoal " << p->getResult() << std::endl;
      Trace("pp-dsl") << "  " << p->getResult() << std::endl;
    }
    d_subgoals.clear();
  }
}

bool ProofPostprocessDsl::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                       const std::vector<Node>& fa,
                                       bool& continueUpdate)
{
  ProofRule id = pn->getRule();
  return id == ProofRule::TRUST || id == ProofRule::TRUST_THEORY_REWRITE;
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
  // don't try if children are non-empty
  if (!children.empty())
  {
    return false;
  }
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
  // if theory rewrite, get diagnostic information
  if (id == ProofRule::TRUST_THEORY_REWRITE)
  {
    builtin::BuiltinProofRuleChecker::getTheoryId(args[1], tid);
    getMethodId(args[2], mid);
  }
  Trace("pp-dsl") << "Prove " << res << " from " << tid << " / " << mid
                  << ", in mode " << d_tmode << std::endl;
  int64_t recLimit = options().proof.proofRewriteRconsRecLimit;
  int64_t stepLimit = options().proof.proofRewriteRconsStepLimit;
  // Attempt to reconstruct the proof of the equality into cdp using the
  // rewrite database proof reconstructor.
  // We record the subgoals in d_subgoals.
  if (d_rdbPc.prove(
          cdp, res[0], res[1], recLimit, stepLimit, d_subgoals, d_tmode))
  {
    // If we made (= res true) above, conclude the original res.
    if (reqTrueElim)
    {
      cdp->addStep(res[0], ProofRule::TRUE_ELIM, {res}, {});
      res = res[0];
    }
    pfgEnsureClosed(options(), res, cdp, "check-dsl", "check dsl");
    // if successful, we update the proof
    return true;
  }
  // otherwise no update
  return false;
}

}  // namespace smt
}  // namespace cvc5::internal
