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
  void ensureSolution();

  std::unique_ptr<context::Context> d_context;

  CoCoA::ring d_polyRing;
  IncrementalTracer d_tracer{};
  context::CDList<CoCoA::RingElem> d_gens;
  context::CDO<std::vector<CoCoA::RingElem>> d_basis;
  context::CDO<bool> d_hasCore;
  context::CDO<std::vector<size_t>> d_core;
  context::CDO<std::optional<bool>> d_hasSolution;
  context::CDO<std::vector<CoCoA::RingElem>> d_solution;
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__GROEBNER_H */

#endif /* CVC5_USE_COCOA */
