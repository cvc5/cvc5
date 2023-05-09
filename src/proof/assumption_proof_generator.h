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
 * The assumption proof generator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ASSUMPTION_PROOF_GENERATOR_H
#define CVC5__PROOF__ASSUMPTION_PROOF_GENERATOR_H

#include "proof/proof_generator.h"

namespace cvc5::internal {

class ProofNodeManager;

/**
 * A proof generator which always returns (ASSUME f) for getProofFor(f).
 */
class AssumptionProofGenerator : public ProofGenerator
{
 public:
  AssumptionProofGenerator(ProofNodeManager* pnm);
  /** Get the proof for formula f */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Identify this generator (for debugging, etc..) */
  std::string identify() const override;

 private:
  /** The proof manager, used for allocating new ProofNode objects */
  ProofNodeManager* d_pnm;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__ASSUMPTION_PROOF_GENERATOR_H */
