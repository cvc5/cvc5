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
 * Proof logger utility.
 */

#include "smt/proof_logger.h"

#include "proof/proof_node_manager.h"
#include "smt/proof_manager.h"

namespace cvc5::internal {

ProofLogger::ProofLogger(Env& env,
                         std::ostream& out,
                         smt::PfManager* pm,
                         smt::Assertions& as,

                         smt::ProofPostprocess* ppp)
    : EnvObj(env),
      d_out(out),
      d_pm(pm),
      d_pnm(pm->getProofNodeManager()),
      d_as(as),
      d_ppp(ppp),
      d_atp(nodeManager()),
      d_alfp(env, d_atp, pm->getRewriteDatabase())
{
  Trace("pf-log-debug") << "Make proof logger" << std::endl;
  // global options on out
  options::ioutils::applyOutputLanguage(out, Language::LANG_SMTLIB_V2_6);
  options::ioutils::applyPrintArithLitToken(out, true);
  options::ioutils::applyPrintSkolemDefinitions(out, true);
}

ProofLogger::~ProofLogger() {}

void ProofLogger::logCnfPreprocessInputs(const std::vector<Node>& inputs) {}

void ProofLogger::logCnfPreprocessInputProofs(std::vector<std::shared_ptr<ProofNode>>& pfns)
{
  Trace("pf-log") << "; log: cnf preprocess input proof start" << std::endl;
  std::shared_ptr<ProofNode> pfn = d_pnm->mkNode(ProofRule::AND_INTRO, pfns, {});
  ProofScopeMode m = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS;
  std::shared_ptr<ProofNode> ppn = d_pm->connectProofToAssertions(pfn, d_as, m);
  d_alfp.print(d_out, ppn, m);
  Trace("pf-log") << "; log: cnf preprocess input proof end" << std::endl;
}

void ProofLogger::logTheoryLemmaProof(std::shared_ptr<ProofNode>& pfn)
{
  d_alfp.printIncremental(d_out, pfn);
}

void ProofLogger::logTheoryLemma(const Node& n)
{
  Trace("pf-log") << "; log theory lemma " << n << std::endl;
  std::shared_ptr<ProofNode> ptl =
      d_pnm->mkTrustedNode(TrustId::THEORY_LEMMA, {}, {}, n);
  d_alfp.printIncremental(d_out, ptl);
}

void ProofLogger::logSatRefutation(const std::vector<Node>& inputs,
                                   const std::vector<Node>& lemmas)
{
  Trace("pf-log") << "; log SAT refutation" << std::endl;
}

void ProofLogger::logSatRefutationProof(std::shared_ptr<ProofNode>& pfn) {}

}  // namespace cvc5::internal
