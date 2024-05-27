/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  if (!d_subgoals.empty())
  {
    std::vector<std::shared_ptr<ProofNode>> sgs = d_subgoals;
    Trace("pp-dsl") << "Also reconstruct proofs for " << sgs.size()
                    << " subgoals..." << std::endl;
    d_subgoals.clear();
    for (std::shared_ptr<ProofNode> p : sgs)
    {
      pnu.process(p);
    }
  }
  // should never construct a subgoal for a step from a subgoal
  if (!d_subgoals.empty())
  {
    Trace("pp-dsl") << "REM SUBGOALS: " << std::endl;
    for (std::shared_ptr<ProofNode> p : d_subgoals)
    {
      Trace("pp-dsl") << "  " << p->getResult() << std::endl;
    }
  }
  Assert(d_subgoals.empty());
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
  int64_t recLimit = options().proof.proofRewriteRconsRecLimit;
  int64_t stepLimit = options().proof.proofRewriteRconsStepLimit;
  // Attempt to reconstruct the proof of the equality into cdp using the
  // rewrite database proof reconstructor.
  // We record the subgoals in d_subgoals.
  if (d_rdbPc.prove(
          cdp, res[0], res[1], tid, mid, recLimit, stepLimit, d_subgoals))
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
