/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Evaluator for separation logic assertions against a concrete heap model.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SEP__SEP_MODEL_CHECKER_H
#define CVC5__THEORY__SEP__SEP_MODEL_CHECKER_H

#include <utility>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {

class TheoryModel;

namespace sep {

/**
 * Utility for evaluating separation logic (spatial) assertions against a
 * concrete heap model, for the purpose of check-model.
 *
 * The heap model produced by TheorySep is a fully concrete structure: a term
 * built from SEP_EMP, SEP_PTO (with constant location/data) and SEP_STAR.
 * Given such a heap, this class decides the truth value of a spatial assertion
 * using the standard separation logic semantics.
 */
class SepModelChecker
{
 public:
  /**
   * Evaluate spatial assertion `a` against the concrete heap model `heap`,
   * using model `m` to evaluate non-spatial subterms (and the concrete
   * location/data values of points-to atoms).
   *
   * @param m The model, used to evaluate non-spatial subterms.
   * @param heap The concrete heap model (SEP_EMP / SEP_PTO / SEP_STAR).
   * @param a The assertion to evaluate.
   * @return the Boolean constant true or false if `a` could be evaluated
   * against `heap`, or the null node if evaluation is not supported (e.g.
   * `a` contains a separation magic wand, whose semantics quantify over all
   * possible extension heaps and cannot be checked against a single model).
   */
  static Node evaluate(const TheoryModel* m, TNode heap, TNode a);

  /**
   * Does `n` contain a subterm whose truth depends on which heap it is
   * evaluated in? Such a term cannot be decided by the generic model
   * evaluator, which has no heap to evaluate it against.
   *
   * Note this counts the internal SEP_LABEL, unlike TheorySep::isSpatialKind,
   * whose caller has already stripped the label from the atom it is testing.
   *
   * @param n The term to test.
   * @return true if `n` has a separation logic subterm of such a kind.
   */
  static bool hasSpatialSubterm(TNode n);

 private:
  /** A single heap cell: a (location, data) pair of constants. */
  using Cell = std::pair<Node, Node>;
  /** A (sub-)heap: a collection of disjoint cells. */
  using Heap = std::vector<Cell>;

  /** Tri-valued evaluation result. */
  enum class Tri
  {
    FALSE = 0,
    TRUE = 1,
    /** could not be evaluated (e.g. an unsupported operator like wand) */
    UNKNOWN = 2,
  };

  SepModelChecker(const TheoryModel* m);

  /**
   * Populate `d_heap` from the heap-model term `heap`. Returns false if the
   * term is not a recognized concrete heap.
   */
  bool extractHeap(TNode heap);
  /**
   * Add the cell described by the points-to term `pto` to `d_heap`. Returns
   * false if its location or data does not evaluate to a constant.
   */
  bool addCell(TNode pto);

  /** Evaluate spatial formula `phi` against sub-heap `h`. */
  Tri eval(TNode phi, const Heap& h);
  /**
   * Collect the location constants of a separation label's set value `setVal`
   * (built from SET_EMPTY / SET_SINGLETON / SET_UNION) into `locs`. Returns
   * false if `setVal` is not a recognized concrete set.
   */
  bool collectLocations(TNode setVal, std::vector<Node>& locs);
  /**
   * Evaluate the separating conjunction of `children[ci..]` against sub-heap
   * `h`, i.e. search for a partition of `h` satisfying every child.
   */
  Tri evalStar(const std::vector<Node>& children, size_t ci, const Heap& h);
  /**
   * If the syntax of `phi` fixes the number of cells any heap satisfying it
   * must have, set `size` to that number and return true. This holds for emp
   * (zero cells), pto (one cell), and separating conjunctions of these (their
   * sum). Returns false for every other formula, whose cell count depends on
   * the heap.
   */
  static bool getExactSize(TNode phi, size_t& size);

  /** Convert a tri-value from a bool. */
  static Tri fromBool(bool b) { return b ? Tri::TRUE : Tri::FALSE; }

  /** The model, used to evaluate non-spatial subterms. */
  const TheoryModel* d_model;
  /** The concrete heap model. */
  Heap d_heap;
  /**
   * The number of candidate fragments the partition search for separating
   * conjunction may still consider. Reaching zero makes every pending star
   * evaluate to UNKNOWN.
   */
  size_t d_budget;
};

}  // namespace sep
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SEP__SEP_MODEL_CHECKER_H */
