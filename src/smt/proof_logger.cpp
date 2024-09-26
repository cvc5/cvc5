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

#include "smt/proof_manager.h"

namespace cvc5::internal {

ProofLogger::ProofLogger(Env& env, smt::PfManager* pm)
    : EnvObj(env), d_pm(pm), d_atp(nodeManager()), d_alfp(env, d_atp, pm->getRewriteDatabase())
{
}

ProofLogger::~ProofLogger() {}

void ProofLogger::logClause(std::shared_ptr<ProofNode>& pfn) {}

void ProofLogger::logClauseFromPreprocessedInput(std::shared_ptr<ProofNode>& pfn)
{
  
}
  
void ProofLogger::logTheoryLemma(const Node& n) {}

}  // namespace cvc5::internal
