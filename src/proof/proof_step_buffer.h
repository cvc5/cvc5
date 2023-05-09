/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof step and proof step buffer utilities.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PROOF_STEP_BUFFER_H
#define CVC5__PROOF__PROOF_STEP_BUFFER_H

#include <vector>

#include "expr/node.h"
#include "proof/proof_rule.h"

namespace cvc5::internal {

class ProofChecker;

/**
 * Information for constructing a step in a CDProof. Notice that the conclusion
 * of the proof step is intentionally not included in this data structure.
 * Instead, it is intended that conclusions may be associated with proof steps
 * based on e.g. the result of proof checking.
 */
class ProofStep
{
 public:
  ProofStep();
  ProofStep(PfRule r,
            const std::vector<Node>& children,
            const std::vector<Node>& args);
  /** The proof rule */
  PfRule d_rule;
  /** The proof children */
  std::vector<Node> d_children;
  /** The proof arguments */
  std::vector<Node> d_args;
};
std::ostream& operator<<(std::ostream& out, ProofStep step);

/**
 * Class used to speculatively try and buffer a set of proof steps before
 * sending them to a proof object.
 */
class ProofStepBuffer
{
 public:
  /**
   * @param pc The proof checker we are using
   * @param ensureUnique Whether we ensure that the conclusions of steps
   * added to this buffer are unique. Later steps with the same conclusion as
   * a previous one are discarded.
   * @param autoSym Whether this proof step buffer is considering symmetry
   * automatically. For example, this should be true if the steps of this buffer
   * are being added to a CDProof with automatic symmetry. This impacts
   * uniqueness of conclusions and whether certain steps are necessary.
   */
  ProofStepBuffer(ProofChecker* pc = nullptr,
                  bool ensureUnique = false,
                  bool autoSym = true);
  ~ProofStepBuffer() {}
  /**
   * Returns the conclusion of the proof step, as determined by the proof
   * checker of the given proof. If this is non-null, then the given step
   * is added to the buffer maintained by this class.
   *
   * If expected is non-null, then this method returns null if the result of
   * checking is not equal to expected. Furthermore note that if proof
   * checking is set to none, this method will always successfully return
   * expected.
   */
  Node tryStep(PfRule id,
               const std::vector<Node>& children,
               const std::vector<Node>& args,
               Node expected = Node::null());
  /** Same as try step, but tracks whether a step was added */
  Node tryStep(bool& added,
               PfRule id,
               const std::vector<Node>& children,
               const std::vector<Node>& args,
               Node expected = Node::null());
  /**
   * Same as above, without checking
   * @return true if a step was added. This may return false if e.g. expected
   * was a duplicate conclusion.
   */
  bool addStep(PfRule id,
               const std::vector<Node>& children,
               const std::vector<Node>& args,
               Node expected);
  /** Multi-step version */
  void addSteps(ProofStepBuffer& psb);
  /** pop step */
  void popStep();
  /** Get num steps */
  size_t getNumSteps() const;
  /** Get steps */
  const std::vector<std::pair<Node, ProofStep>>& getSteps() const;
  /** Clear */
  void clear();

 protected:
  /**
   * Whether this proof step buffer is being added to a CDProof with automatic
   * symmetry. This impacts uniqueness of conclusions and whether certain
   * steps are necessary.
   */
  bool d_autoSym;

 private:
  /** The proof checker*/
  ProofChecker* d_checker;
  /** the queued proof steps */
  std::vector<std::pair<Node, ProofStep>> d_steps;
  /** Whether we are ensuring the conclusions in the buffer are unique */
  bool d_ensureUnique;
  /** The set of conclusions in steps */
  std::unordered_set<Node> d_allSteps;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_STEP_BUFFER_H */
