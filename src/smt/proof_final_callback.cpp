/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of module for final processing proof nodes.
 */

#include "smt/proof_final_callback.h"

#include "options/proof_options.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_manager.h"
#include "smt/smt_statistics_registry.h"
#include "theory/builtin/proof_checker.h"
#include "theory/theory_id.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

ProofFinalCallback::ProofFinalCallback(ProofNodeManager* pnm)
    : d_ruleCount(smtStatisticsRegistry().registerHistogram<PfRule>(
          "finalProof::ruleCount")),
      d_instRuleIds(
          smtStatisticsRegistry().registerHistogram<theory::InferenceId>(
              "finalProof::instRuleId")),
      d_annotationRuleIds(
          smtStatisticsRegistry().registerHistogram<theory::InferenceId>(
              "finalProof::annotationRuleId")),
      d_totalRuleCount(
          smtStatisticsRegistry().registerInt("finalProof::totalRuleCount")),
      d_minPedanticLevel(
          smtStatisticsRegistry().registerInt("finalProof::minPedanticLevel")),
      d_numFinalProofs(
          smtStatisticsRegistry().registerInt("finalProofs::numFinalProofs")),
      d_pnm(pnm),
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
  PfRule r = pn->getRule();
  // if not doing eager pedantic checking, fail if below threshold
  if (options::proofCheck() != options::ProofCheckMode::EAGER)
  {
    if (!d_pedanticFailure)
    {
      Assert(d_pedanticFailureOut.str().empty());
      if (d_pnm->getChecker()->isPedanticFailure(r, d_pedanticFailureOut))
      {
        d_pedanticFailure = true;
      }
    }
  }
  if (options::proofCheck() != options::ProofCheckMode::NONE)
  {
    d_pnm->ensureChecked(pn.get());
  }
  uint32_t plevel = d_pnm->getChecker()->getPedanticLevel(r);
  if (plevel != 0)
  {
    d_minPedanticLevel.minAssign(plevel);
  }
  // record stats for the rule
  d_ruleCount << r;
  ++d_totalRuleCount;
  // take stats on the instantiations in the proof
  if (r == PfRule::INSTANTIATE)
  {
    Node q = pn->getChildren()[0]->getResult();
    const std::vector<Node>& args = pn->getArguments();
    if (args.size() > q[0].getNumChildren())
    {
      InferenceId id;
      if (getInferenceId(args[q[0].getNumChildren()], id))
      {
        d_instRuleIds << id;
      }
    }
  }
  else if (r == PfRule::ANNOTATION)
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
  // print for debugging
  if (TraceIsOn("final-pf-hole"))
  {
    // currently only track theory rewrites
    if (r == PfRule::THEORY_REWRITE)
    {
      const std::vector<Node>& args = pn->getArguments();
      Node eq = args[0];
      TheoryId tid = THEORY_BUILTIN;
      builtin::BuiltinProofRuleChecker::getTheoryId(args[1], tid);
      Trace("final-pf-hole") << "hole " << r << " " << tid << " : " << eq[0]
                             << " ---> " << eq[1] << std::endl;
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
