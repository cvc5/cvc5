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
 * An incremental groebner basis engine.
 */

#include "cvc5_private.h"

#ifdef CVC5_USE_COCOA

#ifndef CVC5__THEORY__FF__GROEBNER_H
#define CVC5__THEORY__FF__GROEBNER_H

#include <CoCoA/RingFp.H>
#include <CoCoA/SparsePolyRing.H>

#include <optional>
#include <vector>

#include "context/cdlist_forward.h"
#include "context/cdo.h"
#include "context/context.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/ff/core.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

// Class for constructing a polynomial ideal for an incremental source of
// generators.
//
// Essentially, you can pass a sequence of generators to this class:
//
//     p1, p2, p3, p4, p5, p6, p7
//
// in chunks. E.g., p1, p2 and then p3, p4, p5, p6, p7. After each chunk, you
// can:
//
// * check if the whole sequence generates a trivial ideal
//   * if so, get a subset of the generators that cause triviality
// * if not, check if the variety (common zero set) for the sequence is empty
// * if not, get a common zero
//
// The class support backtracking/popping: you can remove a chunk of generators
// at any time.
class IncrementalIdeal : EnvObj
{
 public:
  IncrementalIdeal(Env& env, CoCoA::ring polyRing);
  // Add new generators
  void pushGenerators(std::vector<CoCoA::RingElem>&& gens);
  // Is the ideal the whole ring?
  bool idealIsTrivial();
  // For a trivial ideal, return a (sub)list of generator indices that generate it.
  const std::vector<size_t>& trivialCoreIndices();
  // For a trivial ideal, return a (sub)list of generators that generate it.
  std::vector<CoCoA::RingElem> trivialCore();
  // For a non-trivial idea, check whether there is a base-field variety member.
  bool hasSolution();
  // For a non-trivial idea with a base-field variety member, get it.
  const std::vector<CoCoA::RingElem>& solution();
  // Remove the last batch of generators
  void pop();

 private:
  // Run common-root extraction, ensuring a common root is found if one exists.
  void ensureSolution();

  // Used to manage the sequence of generators. A new context is pushed for
  // each new chunk of generators, and popped when they are removed.
  //
  // With this context, other data structures are automatically updated as
  // generators are added/removed.
  std::unique_ptr<context::Context> d_context;

  // The ring that generators/the ideal live in
  CoCoA::ring d_polyRing;
  // Used to record steps in the ideal membership calculus.
  IncrementalTracer d_tracer{};
  // The sequence of generators
  context::CDList<CoCoA::RingElem> d_gens;
  // A GB for the current generators.
  context::CDO<std::vector<CoCoA::RingElem>> d_basis;
  // Whether we've already computed a core for ideal triviality.
  context::CDO<bool> d_hasCore;
  // What that core is.
  context::CDO<std::vector<size_t>> d_core;
  // Whether we've search for a common root, and whether we found one.
  //
  // Empty if we haven't searched. True if we found one, False if not.
  context::CDO<std::optional<bool>> d_hasSolution;

  // What the common root is.
  context::CDO<std::vector<CoCoA::RingElem>> d_solution;
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__GROEBNER_H */

#endif /* CVC5_USE_COCOA */
