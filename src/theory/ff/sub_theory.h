/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A field-specific theory.
 * That is, the sub-theory for GF(p) for some fixed p.
 * Implements Figure 2, "DecisionProcedure" from [OKTB23].
 *
 * [OKTB23]: https://doi.org/10.1007/978-3-031-37703-7_8
 */

#include "cvc5_private.h"

#ifdef CVC5_USE_COCOA

#ifndef CVC5__THEORY__FF__SUB_THEORY_H
#define CVC5__THEORY__FF__SUB_THEORY_H

#include <CoCoA/RingFp.H>

#include <string>
#include <unordered_map>
#include <vector>

#include "context/cdlist_forward.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/ff/stats.h"
#include "theory/ff/util.h"
#include "theory/theory.h"
#include "util/integer.h"
#include "util/result.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/**
 * A solver for a specific, known finite field.
 *
 * While the main ff solver is responsible for all elements in any finite field,
 * this solver just considers a single field. The main ff solver essentially
 * just multiplexes between different sub-solvers.
 *
 * The solver only exposes a subset of the standard SMT theory interface. See
 * the methods below.
 *
 * For now, our implementation assumes that the finite field has prime order.
 */
class SubTheory : protected EnvObj, public FieldObj
{
 public:
  /**
   * Create a new sub-theory.
   *
   * Parameters:
   * * modulus: the size of this field for this theory, a prime.
   */
  SubTheory(Env& env, FfStatistics* stats, Integer modulus);

  /**
   * Assert a fact to this theory.
   */
  void notifyFact(TNode fact);

  /**
   * Check the current facts.
   *
   * Does nothing below full effort.
   */
  Result postCheck(Theory::Effort);

  /**
   * Has a conflict been detected?
   */
  bool inConflict() const;

  /**
   * What is that conflict?
   */
  const std::vector<Node>& conflict() const;

  /**
   * Get a model.
   *
   * Can only be called after a full-effort post-check
   * if inConflict is false.
   */
  const std::unordered_map<Node, Node>& model() const;

 private:
  /**
   * Set the conflict to be all facts.
   */
  void setTrivialConflict();

  /**
   * Facts, in notification order.
   *
   * Contains only the facts in *this specific field*.
   *
   * Uses SAT context.
   */
  context::CDList<Node> d_facts;

  /**
   * Non-empty if we're in a conflict. The vector is the conflict.
   */
  std::vector<Node> d_conflict{};

  /**
   * A model, if we've found one. A map from variable nodes to their constant
   * values. Meaningless if d_conflict is non-empty.
   */
  std::unordered_map<Node, Node> d_model{};

  /**
   * Statistics shared among all finite-field sub-theories.
   */
  FfStatistics* d_stats;
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__SUB_THEORY_H */

#endif /* CVC5_USE_COCOA */
