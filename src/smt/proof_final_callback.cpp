/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Jörg Schurr, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of module for final processing proof nodes.
 */

#include "smt/proof_final_callback.h"

#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/proof_options.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_manager.h"
#include "rewriter/rewrite_proof_rule.h"
#include "smt/env.h"
#include "smt/set_defaults.h"
#include "theory/builtin/proof_checker.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory_id.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

ProofFinalCallback::ProofFinalCallback(Env& env)
    : EnvObj(env),
      d_ruleCount(statisticsRegistry().registerHistogram<ProofRule>(
          "finalProof::ruleCount")),
      d_instRuleIds(statisticsRegistry().registerHistogram<theory::InferenceId>(
          "finalProof::instRuleId")),
      d_annotationRuleIds(
          statisticsRegistry().registerHistogram<theory::InferenceId>(
              "finalProof::annotationRuleId")),
      d_dslRuleCount(statisticsRegistry().registerHistogram<ProofRewriteRule>(
          "finalProof::dslRuleCount")),
      d_theoryRewriteRuleCount(
          statisticsRegistry().registerHistogram<ProofRewriteRule>(
              "finalProof::theoryRewriteRuleCount")),
      d_trustIds(statisticsRegistry().registerHistogram<TrustId>(
          "finalProof::trustCount")),
      d_trustTheoryIdCount(
          statisticsRegistry().registerHistogram<theory::TheoryId>(
              "finalProof::trustTheoryIdCount")),
      d_totalRuleCount(
          statisticsRegistry().registerInt("finalProof::totalRuleCount")),
      d_minPedanticLevel(
          statisticsRegistry().registerInt("finalProof::minPedanticLevel")),
      d_numFinalProofs(
          statisticsRegistry().registerInt("finalProofs::numFinalProofs")),
      d_pedanticFailure(false)
{
  d_minPedanticLevel += 10;
}

void ProofFinalCallback::initializeUpdate()
{
  d_pedanticFailure = false;
  d_pedanticFailureOut.str("");
  ++d_numFinalProofs;
}

bool ProofFinalCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                      const std::vector<Node>& fa,
                                      bool& continueUpdate)
{
  ProofRule r = pn->getRule();
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  Assert(pnm != nullptr);
  // if not doing eager pedantic checking, fail if below threshold
  if (options().proof.proofCheck != options::ProofCheckMode::EAGER)
  {
    if (!d_pedanticFailure)
    {
      Assert(d_pedanticFailureOut.str().empty());
      if (pnm->getChecker()->isPedanticFailure(r, &d_pedanticFailureOut))
      {
        d_pedanticFailure = true;
      }
    }
  }
  if (options().proof.proofCheck != options::ProofCheckMode::NONE)
  {
    pnm->ensureChecked(pn.get());
  }
  uint32_t plevel = pnm->getChecker()->getPedanticLevel(r);
  if (plevel != 0)
  {
    d_minPedanticLevel.minAssign(plevel);
  }
  // record stats for the rule
  d_ruleCount << r;
  ++d_totalRuleCount;
  // if a DSL rewrite, take DSL stat
  if (r == ProofRule::DSL_REWRITE || r == ProofRule::THEORY_REWRITE)
  {
    const std::vector<Node>& args = pn->getArguments();
    ProofRewriteRule di;
    if (rewriter::getRewriteRule(args[0], di))
    {
      if (r == ProofRule::DSL_REWRITE)
      {
        d_dslRuleCount << di;
      }
      else
      {
        d_theoryRewriteRuleCount << di;
      }
    }
  }
  // take stats on the instantiations in the proof
  else if (r == ProofRule::INSTANTIATE)
  {
    Node q = pn->getChildren()[0]->getResult();
    const std::vector<Node>& args = pn->getArguments();
    if (args.size() > 1)
    {
      InferenceId id;
      if (getInferenceId(args[1], id))
      {
        d_instRuleIds << id;
      }
    }
  }
  else if (r == ProofRule::ANNOTATION)
  {
    // we currently assume the annotation is a single inference id
    const std::vector<Node>& args = pn->getArguments();
    if (args.size() > 0)
    {
      InferenceId id;
      if (getInferenceId(args[0], id))
      {
        d_annotationRuleIds << id;
        // Use e.g. `--check-proofs --proof-annotate -t im-pf` to see a list of
        // inference that appear in the final proof.
        Trace("im-pf") << "(inference-pf " << id << " " << pn->getResult()
                       << ")" << std::endl;
        Trace("im-pf-assert")
            << "(assert " << pn->getResult() << ") ; " << id << std::endl;
      }
    }
  }
  else if (r == ProofRule::TRUST)
  {
    TrustId id;
    Trace("final-pf-hole") << "hole TRUST";
    if (getTrustId(pn->getArguments()[0], id))
    {
      d_trustIds << id;
      Trace("final-pf-hole") << " " << id;
    }
    Trace("final-pf-hole") << ": " << pn->getResult() << std::endl;
  }
  else if (r == ProofRule::TRUST_THEORY_REWRITE)
  {
    const std::vector<Node>& args = pn->getArguments();
    Node eq = args[0];
    TheoryId tid = THEORY_BUILTIN;
    builtin::BuiltinProofRuleChecker::getTheoryId(args[1], tid);
    Trace("final-pf-hole") << "hole " << r << " " << tid << " : " << eq[0]
                           << " ---> " << eq[1] << std::endl;
    d_trustTheoryIdCount << tid;
  }
  else if (r == ProofRule::MACRO_REWRITE)
  {
    if (TraceIsOn("final-pf-hole"))
    {
      const std::vector<Node>& args = pn->getArguments();
      Node eq = args[0];
      Trace("final-pf-hole") << "hole " << r << " : " << eq << std::endl;
    }
  }

  if (options().proof.checkProofSteps
      || isOutputOn(OutputTag::TRUSTED_PROOF_STEPS))
  {
    Node conc = pn->getResult();
    ProofChecker* pc = pnm->getChecker();
    if (pc->getPedanticLevel(r) == 0)
    {
      // no need to check
    }
    else
    {
      std::vector<Node> premises;
      const std::vector<std::shared_ptr<ProofNode>>& pnc = pn->getChildren();
      for (const std::shared_ptr<ProofNode>& pncc : pnc)
      {
        premises.push_back(pncc->getResult());
      }
      NodeManager* nm = nodeManager();
      Node query = nm->mkNode(Kind::IMPLIES, nm->mkAnd(premises), conc);
      if (isOutputOn(OutputTag::TRUSTED_PROOF_STEPS))
      {
        output(OutputTag::TRUSTED_PROOF_STEPS)
            << "(trusted-proof-step " << query << ")" << std::endl;
      }
      if (options().proof.checkProofSteps)
      {
        // trust the rewriter here, since the subsolver will rewrite anyways
        query = rewrite(query);
        // We use the original form of the query, which is a logically
        // stronger formula. This may make it possible or easier to prove.
        query = SkolemManager::getOriginalForm(query);
        // set up the subsolver
        Options subOptions;
        subOptions.copyValues(d_env.getOptions());
        smt::SetDefaults::disableChecking(subOptions);
        SubsolverSetupInfo ssi(d_env, subOptions);
        Trace("check-proof-steps")
            << "Check: " << r << " : " << query << std::endl;
        Result res = checkWithSubsolver(query.notNode(), ssi, true, 5000);
        Trace("check-proof-steps") << "...got " << res << std::endl;
        if (res != Result::UNSAT)
        {
          Warning() << "A proof step may not hold: " << r << " proving "
                    << query;
          Warning() << ", result from check-sat was: " << res << std::endl;
          Trace("check-proof-steps")
              << "Original conclusion: " << conc << std::endl;
        }
      }
    }
  }
  return false;
}

bool ProofFinalCallback::wasPedanticFailure(std::ostream& out) const
{
  if (d_pedanticFailure)
  {
    out << d_pedanticFailureOut.str();
    return true;
  }
  return false;
}

}  // namespace smt
}  // namespace cvc5::internal
