/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The abstract proof generator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PROOF_GENERATOR_H
#define CVC5__PROOF__PROOF_GENERATOR_H

#include "expr/node.h"

namespace cvc5 {

class CDProof;
class ProofNode;

/** An overwrite policy for CDProof */
enum class CDPOverwrite : uint32_t
{
  // always overwrite an existing step.
  ALWAYS,
  // overwrite ASSUME with non-ASSUME steps.
  ASSUME_ONLY,
  // never overwrite an existing step.
  NEVER,
};
/** Writes a overwrite policy name to a stream. */
std::ostream& operator<<(std::ostream& out, CDPOverwrite opol);

/**
 * An abstract proof generator class.
 *
 * A proof generator is intended to be used as a utility e.g. in theory
 * solvers for constructing and storing proofs internally. A theory may have
 * multiple instances of ProofGenerator objects, e.g. if it has more than one
 * way of justifying lemmas or conflicts.
 *
 * A proof generator has two main interfaces for generating proofs:
 * (1) getProofFor, and (2) addProofTo. The latter is optional.
 *
 * The addProofTo method can be used as an optimization for avoiding
 * the construction of the ProofNode for a given fact.
 *
 * If no implementation of addProofTo is provided, then addProofTo(f, pf)
 * calls getProofFor(f) and links the topmost ProofNode of the returned proof
 * into pf. Note this top-most ProofNode can be avoided in the addProofTo
 * method.
 */
class ProofGenerator
{
 public:
  ProofGenerator();
  virtual ~ProofGenerator();
  /** Get the proof for formula f
   *
   * This forces the proof generator to construct a proof for formula f and
   * return it. If this is an "eager" proof generator, this function is expected
   * to be implemented as a map lookup. If this is a "lazy" proof generator,
   * this function is expected to invoke a proof producing procedure of the
   * generator.
   *
   * It should be the case that hasProofFor(f) is true.
   *
   * @param f The fact to get the proof for.
   * @return The proof for f.
   */
  virtual std::shared_ptr<ProofNode> getProofFor(Node f);
  /**
   * Add the proof for formula f to proof pf. The proof of f is overwritten in
   * pf based on the policy opolicy.
   *
   * @param f The fact to get the proof for.
   * @param pf The CDProof object to add the proof to.
   * @param opolicy The overwrite policy for adding to pf.
   * @param doCopy Whether to do a deep copy of the proof steps into pf.
   * @return True if this call was sucessful.
   */
  virtual bool addProofTo(Node f,
                          CDProof* pf,
                          CDPOverwrite opolicy = CDPOverwrite::ASSUME_ONLY,
                          bool doCopy = false);
  /**
   * Can we give the proof for formula f? This is used for debugging. This
   * returns false if the generator cannot provide a proof of formula f.
   *
   * Also notice that this function does not require the proof for f to be
   * constructed at the time of this call. Thus, if this is a "lazy" proof
   * generator, it is expected that this call is implemented as a map lookup
   * into the bookkeeping maintained by the generator only.
   *
   * Notice the default return value is true. In other words, a proof generator
   * may choose to override this function to verify the construction, although
   * we do not insist this is the case.
   */
  virtual bool hasProofFor(Node f) { return true; }
  /** Identify this generator (for debugging, etc..) */
  virtual std::string identify() const = 0;
};

}  // namespace cvc5

#endif /* CVC5__PROOF__PROOF_GENERATOR_H */
