/*********************                                                        */
/*! \file icp_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implements a ICP-based solver for nonlinear arithmetic.
 **/

#ifndef CVC4__THEORY__ARITH__ICP__ICP_SOLVER_H
#define CVC4__THEORY__ARITH__ICP__ICP_SOLVER_H

#include "util/real_algebraic_number.h"

#ifdef CVC4_POLY_IMP
#include <poly/polyxx.h>

#include "expr/node.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/icp/candidate.h"
#include "theory/arith/nl/icp/contraction_origins.h"
#include "theory/arith/nl/icp/intersection.h"
#include "theory/arith/nl/icp/variable_bounds.h"
#include "theory/arith/nl/poly_conversion.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace icp {

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
    VariableBounds d_bounds;
    /** The contraction candidates generated from the theory atoms */
    std::vector<Candidate> d_candidates;
    /** The current assignment */
    poly::IntervalAssignment d_assignment;
    /** The origins for the current assignment */
    ContractionOriginManager d_origins;
    /** The conflict, if any way found. Initially the null node */
    Node d_conflict;

    /** Initialized the variable bounds with a variable mapper */
    ICPState(VariableMapper& vm) : d_bounds(vm) {}

    /** Reset this state */
    void reset()
    {
      d_bounds.reset();
      d_candidates.clear();
      d_assignment.clear();
      d_origins = ContractionOriginManager();
      d_conflict = Node();
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

}  // namespace icp
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
#endif