/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility class for Sygus Reconstruct module.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__RCONS_OBLIGATION_INFO_H
#define CVC5__THEORY__QUANTIFIERS__RCONS_OBLIGATION_INFO_H

#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

/**
 * A utility class for Sygus Reconstruct obligations. An obligation is a builtin
 * term t and a SyGuS type T, and indicates that we are trying to build a term
 * of type T whose builtin analog is equivalent to t. The main algorithm encodes
 * each obligation (t, T) as a skolem k of type T to embed obligations in
 * candidate solutions (see d_candSols below). It mainly operates over skolems
 * and stores cooresponding builtin terms and other info in instances of this
 * class. Notice that the SyGuS type T of an obligation is not stored in this
 * class as it can be inferred from the type of the skolem k.
 */
class RConsObligationInfo
{
 public:
  /**
   * Constructor. Default value needed for maps.
   *
   * @param builtin builtin term to reconstruct
   */
  explicit RConsObligationInfo(Node builtin = Node::null());

  /**
   * Add `builtin` to the set of equivalent builtins this class' obligation
   * solves.
   *
   * \note `builtin` MUST be equivalent to the builtin terms in `d_builtins`
   *
   * @param builtin builtin term to add
   */
  void addBuiltin(Node builtin);

  /**
   * @return equivalent builtin terms to reconstruct for this class' obligation
   */
  const std::unordered_set<Node>& getBuiltins() const;

  /**
   * Add candidate solution to the set of candidate solutions for the
   * corresponding obligation.
   *
   * @param candSol the candidate solution to add
   */
  void addCandidateSolution(Node candSol);

  /**
   * @return set of candidate solutions for this class' obligation
   */
  const std::unordered_set<Node>& getCandidateSolutions() const;

  /**
   * Add candidate solution to the set of candidate solutions waiting for the
   * corresponding obligation to be solved.
   *
   * @param candSol the candidate solution to add to watch set
   */
  void addCandidateSolutionToWatchSet(Node candSol);

  /**
   * @return set of candidate solutions waiting for this class' obligation
   * to be solved
   */
  const std::unordered_set<Node>& getWatchSet() const;

  /**
   * Return a string representation of an obligation.
   *
   * @param k An obligation
   * @param obInfo Obligation `k`'s info
   * @return A string representation of `k`
   */
  static std::string obToString(Node k, const RConsObligationInfo& obInfo);

  /**
   * Print all reachable obligations and their candidate solutions from
   * the `root` obligation and its candidate solutions.
   *
   * An obligation is reachable from the `root` obligation if it is the `root`
   * obligation or is needed by one of the candidate solutions of other
   * reachable obligations.
   *
   * For example, if we have:
   *
   * Obs = {c_z1, c_z2, c_z3, c_z4} // list of obligations in rcons algorithm
   * CandSols = {c_z1 -> {(c_+ c_1 c_z2)}, c_z2 -> {(c_- c_z3)},
   *             c_z3 -> {c_x}, c_z4 -> {}}
   * root = c_z1
   *
   * Then, the set of reachable obligations from `root` is {c_z1, c_z2, c_z3}
   *
   * \note requires enabling "sygus-rcons" trace
   *
   * @param root The root obligation to start from
   * @param obInfo a map from obligations to their corresponding infos
   */
  static void printCandSols(
      const Node& root,
      const std::unordered_map<Node, RConsObligationInfo>& obInfo);

 private:
  /** Equivalent builtin terms for this class' obligation.
   *
   * To solve the obligation, one of these builtin terms must be reconstructed
   * in the specified grammar (sygus datatype type) of the obligation.
   */
  std::unordered_set<Node> d_builtins;
  /** A set of candidate solutions to this class' obligation.
   *
   * Each candidate solution is a sygus datatype term containing skolem subterms
   * (sub-obligations). By replacing all sub-obligations with their
   * corresponding solutions, we get a term whose builtin analog rewrites to
   * `d_builtin` and hence solves this obligation. For example, given:
   *   d_builtin = (+ x y)
   * a possible set of candidate solutions would be:
   *   d_candSols = {(c_+ c_z1 c_z2), (c_+ c_x c_z2), (c_+ c_z1 c_y),
   *                 (c_+ c_x c_y)}
   * where c_z1 and c_z2 are skolems. Notice that `d_candSols` may contain a
   * pure term that solves the obligation ((c_+ c_x c_y) in this example).
   */
  std::unordered_set<Node> d_candSols;
  /** A set of candidate solutions waiting for this class' obligation to
   * be solved.
   *
   * In the example above, (c_+ c_z1 c_z2) and (c_+ c_x c_z2) are in
   * the watch-set of c_z2. Similarly, (c_+ c_z1 c_z2) and (c_+ c_z1 c_y) are in
   * the watch-set of c_z1.
   */
  std::unordered_set<Node> d_watchSet;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif  // CVC5__THEORY__QUANTIFIERS__RCONS_OBLIGATION_INFO_H
