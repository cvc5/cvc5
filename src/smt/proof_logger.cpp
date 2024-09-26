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
                         smt::Assertions& as)
    : EnvObj(env),
      d_out(out),
      d_pm(pm),
      d_pnm(pm->getProofNodeManager()),
      d_as(as),
      d_atp(nodeManager()),
      d_alfp(env, d_atp, pm->getRewriteDatabase())
{
  Trace("pf-log") << "Make proof logger" << std::endl;
  // global options on out
  options::ioutils::applyOutputLanguage(out, Language::LANG_SMTLIB_V2_6);
  options::ioutils::applyPrintArithLitToken(out, true);
}

ProofLogger::~ProofLogger() {}

void ProofLogger::logClause(std::shared_ptr<ProofNode>& pfn)
{
  d_alfp.printIncremental(d_out, pfn);
}

void ProofLogger::logClauseForCnfPreprocessInput(
    std::shared_ptr<ProofNode>& pfn)
{
  Trace("pf-log") << "Log cnf preprocess input proof" << std::endl;
  ProofScopeMode m = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS;
  std::shared_ptr<ProofNode> ppn = d_pm->connectProofToAssertions(pfn, d_as, m);
  d_alfp.print(d_out, ppn, m);
}

void ProofLogger::logTheoryLemma(const Node& n)
{
  Trace("pf-log") << "Log theory lemma " << n << std::endl;
  std::shared_ptr<ProofNode> ptl =
      d_pnm->mkTrustedNode(TrustId::THEORY_LEMMA, {}, {}, n);
  d_alfp.printIncremental(d_out, ptl);
}

}  // namespace cvc5::internal
