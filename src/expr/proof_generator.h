/*********************                                                        */
/*! \file proof_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The abstract proof generator class
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_GENERATOR_H
#define CVC4__EXPR__PROOF_GENERATOR_H

#include "expr/node.h"
#include "expr/proof_node.h"

namespace CVC4 {

/**
 * An abstract proof generator class, to be used in combination with
 * ProofOutputChannel (see theory/proof_output_channel.h).
 *
 * A proof generator is intended to be used as a utility in theory
 * solvers for constructing and storing proofs internally. A Theory may have
 * multiple instances of ProofGenerator objects, e.g. if it has more than one
 * way of justifying lemmas or conflicts.
 */
class ProofGenerator
{
 public:
  ProofGenerator() {}
  virtual ~ProofGenerator() {}
  /** Get the proof for formula f
   *
   * This forces the proof generator to construct a proof for formula f and
   * return it. If this is an "eager" proof generator, this function is expected
   * to be implemented as a map lookup. If this is a "lazy" proof generator,
   * this function is expected to invoke a proof producing procedure of the
   * generator.
   *
   * It should be the case that hasProofFor(f) is true.
   */
  virtual std::shared_ptr<ProofNode> getProofFor(Node f) = 0;
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
  /**
   * Identify this generator (for debugging, etc..)
   */
  virtual std::string identify() const = 0;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_GENERATOR_H */
