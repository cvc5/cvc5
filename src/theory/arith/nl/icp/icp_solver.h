/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements a ICP-based solver for nonlinear arithmetic.
 */

#ifndef CVC5__THEORY__ARITH__ICP__ICP_SOLVER_H
#define CVC5__THEORY__ARITH__ICP__ICP_SOLVER_H

#include "cvc5_private.h"

#ifdef CVC5_POLY_IMP
#include <poly/polyxx.h>
#endif /* CVC5_POLY_IMP */

#include "expr/node.h"
#include "theory/arith/bound_inference.h"
#include "theory/arith/nl/icp/candidate.h"
#include "theory/arith/nl/icp/contraction_origins.h"
#include "theory/arith/nl/icp/intersection.h"
#include "theory/arith/nl/poly_conversion.h"

namespace cvc5 {
namespace theory {
namespace arith {

class InferenceManager;

namespace nl {
namespace icp {

#ifdef CVC5_POLY_IMP

/**
 * This class implements an ICP-based solver. As it is intended to be used in
 * conjunction with other solvers, it only performs contractions, but does not
 * issue splits.
 *
 * In essence, interval constraint propagation has candidates (like x = y^2-z),
 * evaluates their right hand side over the current (interval) assignment and
 * uses the resulting interval to make the interval of the left-hand side
 * variable smaller (contract it).
 *
 * These contractions can yield to a conflict (if the interval of some variable
 * becomes empty) or shrink the search space for a variable.
 */
class ICPSolver
{
  /**
   * This encapsulates the state of the ICP solver that is local to a single
   * theory call. It contains the variable bounds and candidates derived from
   * the assertions, the origins manager and the last conflict.
   */
  struct ICPState
  {
    /** The variable bounds extracted from the input assertions */
    BoundInference d_bounds;
    /** The contraction candidates generated from the theory atoms */
    std::vector<Candidate> d_candidates;
    /** The current assignment */
    poly::IntervalAssignment d_assignment;
    /** The origins for the current assignment */
    ContractionOriginManager d_origins;
    /** The conflict, if any way found. Initially empty */
    std::vector<Node> d_conflict;

    /** Initialized the variable bounds with a variable mapper */
    ICPState(VariableMapper& vm) {}

    /** Reset this state */
    void reset()
    {
      d_bounds = BoundInference();
      d_candidates.clear();
      d_assignment.clear();
      d_origins = ContractionOriginManager();
      d_conflict.clear();
    }
  };

  /** Maps Node (variables) to poly::Variable */
  VariableMapper d_mapper;
  /** The inference manager */
  InferenceManager& d_im;
  /** Cache candidates to avoid reconstruction for every theory call */
  std::map<Node, std::vector<Candidate>> d_candidateCache;
  /** The current state */
  ICPState d_state;

  /** The remaining budget */
  std::int64_t d_budget = 0;
  /** The budget increment for new candidates and strong contractions */
  static constexpr std::int64_t d_budgetIncrement = 10;

  /** Collect all variables from a node */
  std::vector<Node> collectVariables(const Node& n) const;
  /** Construct all possible candidates from a given theory atom */
  std::vector<Candidate> constructCandidates(const Node& n);
  /** Add the given node as candidate */
  void addCandidate(const Node& n);
  /** Initialize the origin manager from the variable bounds */
  void initOrigins();

  /**
   * Perform one contraction with every candidate.
   * If any candidate yields a conflict stops immediately and returns
   * PropagationResult::CONFLICT. If any candidate yields a contraction returns
   * PropagationResult::CONTRACTED. Otherwise returns
   * PropagationResult::NOT_CHANGED.
   */
  PropagationResult doPropagationRound();

  /**
   * Construct lemmas for all bounds that have been improved.
   * For every improved bound, all origins are collected and a lemma of the form
   *   (and origins)  ==>  (new bound)
   * is constructed.
   */
  std::vector<Node> generateLemmas() const;

 public:
  ICPSolver(InferenceManager& im) : d_im(im), d_state(d_mapper) {}
  /** Reset this solver for the next theory call */
  void reset(const std::vector<Node>& assertions);

  /**
   * Performs a full ICP check.
   */
  void check();
};

#else /* CVC5_POLY_IMP */

class ICPSolver
{
 public:
  ICPSolver(InferenceManager& im) {}
  void reset(const std::vector<Node>& assertions);
  void check();
};

#endif /* CVC5_POLY_IMP */

}  // namespace icp
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif
