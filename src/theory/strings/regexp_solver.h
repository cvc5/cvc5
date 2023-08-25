/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Regular expression solver for the theory of strings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__REGEXP_SOLVER_H
#define CVC5__THEORY__STRINGS__REGEXP_SOLVER_H

#include <map>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/strings/extf_solver.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/regexp_operation.h"
#include "theory/strings/sequences_stats.h"
#include "theory/strings/skolem_cache.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/term_registry.h"
#include "util/string.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

class RegExpSolver : protected EnvObj
{
  typedef context::CDList<Node> NodeList;
  typedef context::CDHashMap<Node, bool> NodeBoolMap;
  typedef context::CDHashMap<Node, int> NodeIntMap;
  typedef context::CDHashMap<Node, unsigned> NodeUIntMap;
  typedef context::CDHashMap<Node, Node> NodeNodeMap;
  typedef context::CDHashSet<Node> NodeSet;

 public:
  RegExpSolver(Env& env,
               SolverState& s,
               InferenceManager& im,
               TermRegistry& tr,
               CoreSolver& cs,
               ExtfSolver& es,
               SequencesStatistics& stats);
  ~RegExpSolver() {}

  /** check regular expression memberships
   *
   * This checks the satisfiability of all regular expression memberships
   * of the form (not) s in R. We use various heuristic techniques based on
   * unrolling, combined with techniques from Liang et al, "A Decision Procedure
   * for Regular Membership and Length Constraints over Unbounded Strings",
   * FroCoS 2015.
   */
  void checkMemberships(Theory::Effort e);
  /**
   * Check regular expression memberships eagerly, before running the CAV 14
   * procedure for word equations. Adds lemmas based on our strategy involving
   * reductions or simplifications.
   */
  void checkMembershipsEager();

 private:
  /** compute asserted memberships, store in d_assertedMems */
  void computeAssertedMemberships();
  /** Compute active extended terms of kind k, grouped by representative. */
  std::map<Node, std::vector<Node>> computeAssertions(Kind k) const;
  /**
   * Check inclusions,
   * Assumes d_assertedMems has been computed.
   */
  void checkInclusions();
  /**
   * Check evaluations, which applies substitutions for normal forms to
   * regular expression memberships and evaluates them, and also calls
   * other methods (e.g. partial derivative computations) for the purposes
   * of discovering conflictx.
   * Assumes d_assertedMems has been computed.
   */
  void checkEvaluations();
  /**
   * Check unfold, which unfolds regular expression memberships based on the
   * effort level.
   * Assumes d_assertedMems has been computed.
   */
  void checkUnfold(Theory::Effort effort);
  /**
   * Check memberships in equivalence class for regular expression
   * inclusion.
   *
   * This method returns false if it discovered a conflict for this set of
   * assertions, and true otherwise. It discovers a conflict e.g. if mems
   * contains str.in.re(xi, Ri) and ~str.in.re(xj, Rj) and Rj includes Ri.
   *
   * @param mems Vector of memberships of the form: (~)str.in.re(x1, R1)
   *             ... (~)str.in.re(xn, Rn) where x1 = ... = xn in the
   *             current context. The function removes elements from this
   *             vector that were marked as reduced.
   * @return False if a conflict was detected, true otherwise
   */
  bool checkEqcInclusion(std::vector<Node>& mems);

  /**
   * Check memberships for equivalence class.
   * The vector mems is a vector of memberships of the form:
   *   (~) (x1 in R1 ) ... (~) (xn in Rn)
   * where x1 = ... = xn in the current context.
   *
   * This method may add lemmas or conflicts via the inference manager.
   *
   * This method returns false if it discovered a conflict for this set of
   * assertions, and true otherwise. It discovers a conflict e.g. if mems
   * contains (xi in Ri) and (xj in Rj) and intersect(xi,xj) is empty.
   */
  bool checkEqcIntersect(const std::vector<Node>& mems);
  /**
   * Return true if we should process regular expression unfoldings with
   * the given polarity at the given effort.
   */
  bool shouldUnfold(Theory::Effort e, bool pol) const;
  /**
   * Add the unfolding lemma for asserted regular expression membership
   * assertion. Return true if a lemma was successfully sent to the inference
   * manager.
   */
  bool doUnfold(const Node& assertion);
  // Constants
  Node d_emptyString;
  Node d_emptyRegexp;
  Node d_true;
  Node d_false;
  /** The solver state of the parent of this object */
  SolverState& d_state;
  /** the output channel of the parent of this object */
  InferenceManager& d_im;
  /** reference to the core solver, used for certain queries */
  CoreSolver& d_csolver;
  /** reference to the extended function solver of the parent */
  ExtfSolver& d_esolver;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
  /**
   * Check partial derivative
   *
   * Returns false if a lemma pertaining to checking the partial derivative
   * of x in r was added. In this case, addedLemma is updated to true.
   *
   * The argument atom is the assertion that explains x in r, which is the
   * normalized form of atom that may be modified using a substitution whose
   * explanation is nf_exp.
   */
  bool checkPDerivative(Node x, Node r, Node atom, std::vector<Node>& nf_exp);
  cvc5::internal::String getHeadConst(Node x);
  bool deriveRegExp(Node x, Node r, Node atom, std::vector<Node>& ant);
  Node getNormalSymRegExp(Node r, std::vector<Node>& nf_exp);
  /** regular expression operation module */
  RegExpOpr d_regexp_opr;
  /** Asserted memberships, cached during a full effort check */
  std::map<Node, std::vector<Node>> d_assertedMems;
}; /* class TheoryStrings */

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__THEORY_STRINGS_H */
