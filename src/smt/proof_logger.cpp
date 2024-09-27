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
      d_pm(pm),
      d_pnm(pm->getProofNodeManager()),
      d_as(as),
      d_ppp(ppp),
      d_atp(nodeManager()),
      d_alfp(env, d_atp, pm->getRewriteDatabase()),
      d_aout(out, d_alfp.getLetBinding(), "@t", false)
{
  Trace("pf-log-debug") << "Make proof logger" << std::endl;
  // global options on out
  options::ioutils::applyOutputLanguage(out, Language::LANG_SMTLIB_V2_6);
  options::ioutils::applyPrintArithLitToken(out, true);
  options::ioutils::applyPrintSkolemDefinitions(out, true);
}

ProofLogger::~ProofLogger() {}

void ProofLogger::logCnfPreprocessInputs(const std::vector<Node>& inputs) {}

void ProofLogger::logCnfPreprocessInputProofs(
    std::vector<std::shared_ptr<ProofNode>>& pfns)
{
  Trace("pf-log") << "; log: cnf preprocess input proof start" << std::endl;
  std::shared_ptr<ProofNode> pfn =
      d_pnm->mkNode(ProofRule::AND_INTRO, pfns, {});
  ProofScopeMode m = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS;
  d_ppProof = d_pm->connectProofToAssertions(pfn, d_as, m);
  d_alfp.print(d_aout, d_ppProof, m);
  Trace("pf-log") << "; log: cnf preprocess input proof end" << std::endl;
}

void ProofLogger::logTheoryLemmaProof(std::shared_ptr<ProofNode>& pfn)
{
  Trace("pf-log") << "; log theory lemma proof start " << pfn->getResult()
                  << std::endl;
  d_lemmaPfs.emplace_back(pfn);
  d_alfp.print(d_aout, pfn, ProofScopeMode::NONE);
  Trace("pf-log") << "; log theory lemma proof end" << std::endl;
}

void ProofLogger::logTheoryLemma(const Node& n)
{
  Trace("pf-log") << "; log theory lemma start " << n << std::endl;
  std::shared_ptr<ProofNode> ptl =
      d_pnm->mkTrustedNode(TrustId::THEORY_LEMMA, {}, {}, n);
  d_lemmaPfs.emplace_back(ptl);
  d_alfp.print(d_aout, ptl, ProofScopeMode::NONE);
  Trace("pf-log") << "; log theory lemma end" << std::endl;
}

void ProofLogger::logSatRefutation(const std::vector<Node>& inputs,
                                   const std::vector<Node>& lemmas)
{
  Trace("pf-log") << "; log SAT refutation start" << std::endl;
  // TODO: connect and print the single step?
  Trace("pf-log") << "; log SAT refutation end" << std::endl;
}

void ProofLogger::logSatRefutationProof(std::shared_ptr<ProofNode>& pfn)
{
  Trace("pf-log") << "; log SAT refutation proof start" << std::endl;
  // TODO: connect?
  d_alfp.print(d_aout, pfn, ProofScopeMode::NONE);
  Trace("pf-log") << "; log SAT refutation proof end" << std::endl;
}

}  // namespace cvc5::internal
