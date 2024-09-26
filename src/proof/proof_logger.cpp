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

  ProofLogger::ProofLogger(Env& env) : EnvObj(env){}
  ProofLogger::~ProofLogger() {}
  void ProofLogger::logProof(std::shared_ptr<ProofNode>& pfn){}

}  // namespace cvc5::internal
