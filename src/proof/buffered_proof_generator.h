/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A proof generator for buffered proof steps.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__BUFFERED_PROOF_GENERATOR_H
#define CVC5__PROOF__BUFFERED_PROOF_GENERATOR_H

#include "context/cdhashmap.h"
#include "proof/proof_generator.h"

namespace cvc5 {

class ProofNodeManager;
class ProofStep;

/**
 * The proof generator for buffered steps. This class is a context-dependent
 * mapping from formulas to proof steps. It does not generate ProofNodes until
 * it is asked to provide a proof for a given fact.
 */
class BufferedProofGenerator : public ProofGenerator
{
  typedef context::CDHashMap<Node, std::shared_ptr<ProofStep>> NodeProofStepMap;

 public:
  BufferedProofGenerator(context::Context* c, ProofNodeManager* pnm);
  ~BufferedProofGenerator() {}
  /** add step
   * Unless the overwrite policy is ALWAYS it does not replace previously
   * registered steps (modulo (dis)equality symmetry).
   */
  bool addStep(Node fact,
               ProofStep ps,
               CDPOverwrite opolicy = CDPOverwrite::NEVER);
  /** Get proof for. It is robust to (dis)equality symmetry. */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Whether a step has been registered for f. */
  bool hasProofFor(Node f) override;
  /** identify */
  std::string identify() const override { return "BufferedProofGenerator"; }

 private:
  /** maps expected to ProofStep */
  NodeProofStepMap d_facts;
  /** the proof node manager */
  ProofNodeManager* d_pnm;
};

}  // namespace cvc5

#endif /* CVC5__PROOF__BUFFERED_PROOF_GENERATOR_H */
