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

#include "proof/proof_logger.h"

namespace cvc5::internal {

ProofLogger::ProofLogger(Env& env, rewriter::RewriteDb* rdb) : EnvObj(env), d_atp(nodeManager()), d_alfp(env, d_atp, rdb) {}

ProofLogger::~ProofLogger() {}

void ProofLogger::logInputClause(std::shared_ptr<ProofNode>& pfn)
{
}

void ProofLogger::logTheoryLemma(const Node& n)
{
  
}

}  // namespace cvc5::internal
