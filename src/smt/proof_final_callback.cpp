/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Joerg Schurr, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
#include "proof/alf/alf_printer.h"
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
      d_ruleEouCount(statisticsRegistry().registerHistogram<ProofRule>(
          "finalProof::ruleUnhandledEoCount")),
      d_instRuleIds(statisticsRegistry().registerHistogram<theory::InferenceId>(
          "finalProof::instRuleId")),
      d_dslRuleCount(statisticsRegistry().registerHistogram<ProofRewriteRule>(
          "finalProof::dslRuleCount")),
      d_theoryRewriteRuleCount(
          statisticsRegistry().registerHistogram<ProofRewriteRule>(
              "finalProof::theoryRewriteRuleCount")),
      d_theoryRewriteEouCount(
          statisticsRegistry().registerHistogram<ProofRewriteRule>(
              "finalProof::theoryRewriteRuleUnhandledEoCount")),
      d_trustIds(statisticsRegistry().registerHistogram<TrustId>(
          "finalProof::trustCount")),
      d_trustTheoryRewriteCount(
          statisticsRegistry().registerHistogram<theory::TheoryId>(
              "finalProof::trustTheoryRewriteCount")),
      d_trustTheoryLemmaCount(
          statisticsRegistry().registerHistogram<theory::TheoryId>(
              "finalProof::trustTheoryLemmaCount")),
      d_totalRuleCount(
          statisticsRegistry().registerInt("finalProof::totalRuleCount")),
      d_minPedanticLevel(
          statisticsRegistry().registerInt("finalProof::minPedanticLevel")),
      d_numFinalProofs(
          statisticsRegistry().registerInt("finalProofs::numFinalProofs")),
      d_pedanticFailure(false),
      d_checkProofHoles(false)
{
  d_minPedanticLevel += 10;
}

void ProofFinalCallback::initializeUpdate()
{
  d_pedanticFailure = false;
  d_pedanticFailureOut.str("");
  ++d_numFinalProofs;
  d_checkProofHoles =
      options().base.statisticsInternal || options().proof.checkProofsComplete;
}

void ProofFinalCallback::finalize(std::shared_ptr<ProofNode> pn)
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
  // if not taking statistics or checking completeness, don't bother computing
  // the following
  if (d_checkProofHoles)
  {
    // record stats for the rule
    d_ruleCount << r;
    bool isHandled = proof::AlfPrinter::isHandled(options(), pn.get());
    if (!isHandled)
    {
      d_ruleEouCount << r;
    }
    ++d_totalRuleCount;
    TheoryId trustTid = THEORY_BUILTIN;
    TrustId trustId = TrustId::NONE;
    ProofRewriteRule dslId = ProofRewriteRule::NONE;
    // if a DSL rewrite, take DSL stat
    if (r == ProofRule::DSL_REWRITE || r == ProofRule::THEORY_REWRITE)
    {
      const std::vector<Node>& args = pn->getArguments();
      rewriter::getRewriteRule(args[0], dslId);
      Assert(dslId != ProofRewriteRule::NONE);
      if (r == ProofRule::DSL_REWRITE)
      {
        d_dslRuleCount << dslId;
      }
      else
      {
        if (!isHandled)
        {
          d_theoryRewriteEouCount << dslId;
        }
        d_theoryRewriteRuleCount << dslId;
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
    else if (r == ProofRule::TRUST)
    {
      if (getTrustId(pn->getArguments()[0], trustId))
      {
        d_trustIds << trustId;
        if (trustId == TrustId::THEORY_LEMMA)
        {
          const std::vector<Node>& args = pn->getArguments();
          if (args.size() >= 3)
          {
            builtin::BuiltinProofRuleChecker::getTheoryId(args[2], trustTid);
          }
          d_trustTheoryLemmaCount << trustTid;
        }
      }
    }
    else if (r == ProofRule::TRUST_THEORY_REWRITE)
    {
      const std::vector<Node>& args = pn->getArguments();
      Node eq = args[0];
      builtin::BuiltinProofRuleChecker::getTheoryId(args[1], trustTid);
      d_trustTheoryRewriteCount << trustTid;
    }
    // If the rule is not handled, and we are checking for complete proofs
    if (!isHandled && options().proof.checkProofsComplete)
    {
      // internal error if hardFailure is true
      std::stringstream ss;
      ss << "The proof was incomplete";
      if (r == ProofRule::TRUST)
      {
        ss << " due to a trust step with id " << trustId;
        if (trustId == TrustId::THEORY_LEMMA)
        {
          ss << ", from theory " << trustTid;
        }
      }
      else if (r == ProofRule::TRUST_THEORY_REWRITE)
      {
        ss << " due to a trusted theory rewrite from theory " << trustTid;
      }
      else if (r == ProofRule::THEORY_REWRITE)
      {
        ss << " due to an unhandled instance of rewrite rule " << dslId;
      }
      else
      {
        ss << " due to an unhandled instance of proof rule " << r;
      }
      ss << ".";
      InternalError() << ss.str();
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
      Node query = conc;
      if (!premises.empty())
      {
        query = nm->mkNode(Kind::IMPLIES, nm->mkAnd(premises), query);
      }
      // print the trusted step information
      if (isOutputOn(OutputTag::TRUSTED_PROOF_STEPS))
      {
        output(OutputTag::TRUSTED_PROOF_STEPS)
            << "(trusted-proof-step " << query;
        output(OutputTag::TRUSTED_PROOF_STEPS) << " :rule " << r;
        TheoryId tid = THEORY_LAST;
        if (r == ProofRule::TRUST)
        {
          TrustId id;
          if (getTrustId(pn->getArguments()[0], id))
          {
            output(OutputTag::TRUSTED_PROOF_STEPS) << " :trust-id " << id;
            if (id == TrustId::THEORY_LEMMA)
            {
              const std::vector<Node>& args = pn->getArguments();
              if (args.size() >= 3)
              {
                builtin::BuiltinProofRuleChecker::getTheoryId(args[2], tid);
              }
            }
          }
        }
        else if (r == ProofRule::TRUST_THEORY_REWRITE)
        {
          const std::vector<Node>& args = pn->getArguments();
          builtin::BuiltinProofRuleChecker::getTheoryId(args[1], tid);
        }
        if (tid != THEORY_LAST)
        {
          output(OutputTag::TRUSTED_PROOF_STEPS) << " :theory " << tid;
        }
        output(OutputTag::TRUSTED_PROOF_STEPS) << ")" << std::endl;
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
