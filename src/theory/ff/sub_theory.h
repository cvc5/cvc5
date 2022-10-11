/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A field-specific theory
 */

#include "cvc5_private.h"

#ifdef CVC5_USE_COCOA

#ifndef CVC5__THEORY__FF__SUB_THEORY_H
#define CVC5__THEORY__FF__SUB_THEORY_H

#include <CoCoA/RingFp.H>

#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "context/cdlist_forward.h"
#include "context/cdo.h"
#include "context/context.h"
#include "expr/node.h"
#include "options/ff_options.h"
#include "smt/env_obj.h"
#include "theory/ff/core.h"
#include "theory/ff/groebner.h"
#include "theory/ff/stats.h"
#include "theory/theory.h"
#include "util/integer.h"

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
class SubTheory : protected EnvObj, protected context::ContextNotifyObj
{
 public:
  // Create a new sub-theory.
  //
  // Parameters:
  // * modulus: the size of this field for this theory, a prime.
  SubTheory(Env& env, FfStatistics* stats, Integer modulus);

  // Notify this theory of a node it may need to handle.
  //
  // All nodes this theory sees in the future must be pre-registered.
  void preRegisterTerm(TNode);

  // Assert a fact to this theory.
  void notifyFact(TNode fact);

  // Check the current facts.
  void postCheck(Theory::Effort);

  // Has a conflict been detected?
  bool inConflict() const;

  // What is that conflict?
  const std::vector<Node>& conflict() const;

  // Get a model.
  //
  // Can only be called after a full-effort post-check
  // if inConflict is false.
  const std::unordered_map<Node, Node>& model() const;

 private:
  // Called on SAT pop; we pop the incremental ideal if needed.
  void contextNotifyPop() override;

  // Compute a Groebner basis for the facts up to (not including) this index.
  void computeBasis(size_t factIndex);

  void extractModel();

  // Initialize the polynomial ring, set up post-registration data structures.
  void ensureInitPolyRing();

  // Uninitialize the polynomial ring, clear post-registration data structures.
  void clearPolyRing();

  // Translate t to CoCoA, and cache the result.
  void translate(TNode t);

  // Is registration done and the polynomial ring initialized?
  bool d_registrationDone();

  // Manages the incremental GB.
  std::optional<IncrementalIdeal> d_incrementalIdeal{};

  // For an atom x == y, contains the potential inverse of (x - y).
  //
  // Used to make x != y.
  std::unordered_map<Node, CoCoA::RingElem> d_atomInverses{};

  // Facts, in notification order.
  //
  // Contains only the facts in *this specific field*.
  //
  // Uses SAT context.
  context::CDList<Node> d_facts;

  // The length of that fact list at each check.
  std::vector<size_t> d_checkIndices{};

  // The length of that fact list at each point where we updated the ideal.
  std::vector<size_t> d_updateIndices{};

  // Non-empty if we're in a conflict.
  std::vector<Node> d_conflict{};

  // Cache from nodes to CoCoA polynomials.
  std::unordered_map<Node, CoCoA::RingElem> d_translationCache{};

  // A model, if we've found one. A map from variable nodes to their constant
  // values.
  std::unordered_map<Node, Node> d_model{};

  // Variables
  context::CDList<Node> d_vars;

  // Variables
  std::unordered_map<size_t, Node> d_symbolIdxVars{};

  // Atoms
  context::CDList<Node> d_atoms;

  // Statistics shared among all finite-field sub-theories.
  FfStatistics* d_stats;
  // The base field of the multivariate polynomial ring.
  //
  // That is, the field that the polynomial coefficients live in/the
  // finite-field constants live in.
  //
  // For now, we assume this is a prime-order finite-field.
  CoCoA::ring d_baseRing;
  // The prime modulus for the base field.
  Integer d_modulus;
  // Set after registration is done.
  std::optional<CoCoA::ring> d_polyRing{};
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__SUB_THEORY_H */

#endif /* CVC5_USE_COCOA */
