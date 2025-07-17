/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Valid witness proof generator utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__VALID_WITNESS_PROOF_GENERATOR_H
#define CVC5__PROOF__VALID_WITNESS_PROOF_GENERATOR_H

#include "cvc5/cvc5_proof_rule.h"
#include "proof/method_id.h"
#include "proof/proof_generator.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class ProofNode;
class ProofNodeManager;

/**
 * Proof generator expected to prove axioms for all witness terms
 * (witness x. P) introduced.
 */
class ValidWitnessProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  /**
   * @param env Reference to the environment
   */
  ValidWitnessProofGenerator(Env& env);
  virtual ~ValidWitnessProofGenerator();
  /**
   * Get proof for fact. This is expected to be a formula returned by mkAxiom.
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** identify */
  std::string identify() const override;
  /** 
   * Make the appropriate witness term for proof rule r with arguments args.
   * This is a term (WITNESS (BOUND_VAR_LIST v) F (INST_PATTERN_LIST attr))
   * where v is a canonical variable for (r, args), F is mkAxiom(nm, v, r args),
   * and attr is a "proof spec" attribute node storing (r, args).
   * @param nm Pointer to the node manager.
   * @param r The proof rule.
   * @param args The arguments to the proof rule.
   * @return The witness term.
   */
  static Node mkWitness(NodeManager* nm,
                        ProofRule r,
                        const std::vector<Node>& args);
  /**
   * Make the conclusion of proof rule r with the given arguments.
   * @param nm Pointer to the node manager.
   * @param v The variable to instantiate the axiom with.
   * @param r The proof rule.
   * @param args The arguments to the proof rule.
   * @return The conclusion of rule r with the given arguments, witnessed by v.
   */
  static Node mkAxiom(NodeManager* nm,
                      const Node& v,
                      ProofRule r,
                      const std::vector<Node>& args);
  /**
   * Make the skolem that witnesses the conclusion of proof rule r with
   * the given arguments.
   * @param nm Pointer to the node manager.
   * @param r The proof rule.
   * @param args The arguments to the proof rule.
   * @return The skolem that witnesses the conclusion of rule r with the given
   * arguments.
   */
  static Node mkSkolem(NodeManager* nm,
                       ProofRule r,
                       const std::vector<Node>& args);

  /**
   * Get proof spec from attribute. This sets r and args based on the
   * information stored in the attribute node attr.
   * @param nm Pointer to the node manager.
   * @param attr The instantiation attribute node.
   * @param r The proof rule stored for attr.
   * @param args The arguments to the proof rule stored for attr.
   * @return true if the information r and args was successfully extracted.
   */
  static bool getProofSpec(NodeManager* nm,
                           const Node& attr,
                           ProofRule& r,
                           std::vector<Node>& args);
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__VALID_WITNESS_PROOF_GENERATOR_H */
