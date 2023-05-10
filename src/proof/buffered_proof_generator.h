/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "smt/env_obj.h"

namespace cvc5::internal {

class ProofNodeManager;
class ProofStep;

/**
 * The proof generator for buffered steps. This class is a context-dependent
 * mapping from formulas to proof steps. It does not generate ProofNodes until
 * it is asked to provide a proof for a given fact.
 */
class BufferedProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  /** Constructor
   *
   * @param env Reference to the environment
   * @param c Pointer to a context to make this object dependent on
   * @param mkUniqueAssume Whether to restrict the proof nodes generated when
   * proofs are requested so that the same ASSUMPTION step is used for repeated
   * premises. Note that this can only be done safely if the user of this
   * buffered proof generator does not use SCOPE steps, which would have the
   * danger of mixing the scopes of assumptions.
   * @param autoSymm Whether the proof requestes are robust to (dis)equality
   * symmetry.
   */
  BufferedProofGenerator(Env& env,
                         context::Context* c,
                         bool mkUniqueAssume = false,
                         bool autoSymm = true);
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

 protected:
  using NodeProofStepMap = context::CDHashMap<Node, std::shared_ptr<ProofStep>>;
  using NodeProofNodeMap = context::CDHashMap<Node, std::shared_ptr<ProofNode>>;

  /** maps expected to ProofStep */
  NodeProofStepMap d_facts;
  /** whether we are forcing unique assumptions */
  bool d_mkUniqueAssume;
  /** whether we automatically add symmetry steps */
  bool d_autoSymm;
  /** Cache of ASSUMPTION proof nodes for nodes used as assumptions in proof
   * steps. Used only if d_mkUniqueAssume is true. */
  NodeProofNodeMap d_assumptionsToPfNodes;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__BUFFERED_PROOF_GENERATOR_H */
