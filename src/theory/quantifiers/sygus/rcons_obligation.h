/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility class for Sygus Reconstruct module.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__RCONS_OBLIGATION_H
#define CVC5__THEORY__QUANTIFIERS__RCONS_OBLIGATION_H

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * A class for holding Sygus Reconstruct obligations. An obligation is a builtin
 * term t and a SyGuS type T, and indicates that we are trying to build a term
 * of type T whose builtin analog is equivalent to t. This class encodes each
 * obligation (T, t) as a skolem k of type T to embed obligations in candidate
 * solutions (see d_candSols below). Notice that the SyGuS type T of an
 * obligation is not stored in this class as it can be inferred from the type of
 * the skolem k.
 */
class RConsObligation
{
 public:
  /**
   * Constructor. Default value needed for maps.
   *
   * @param stn sygus datatype type to reconstruct `t` into
   * @param t builtin term to reconstruct
   */
  RConsObligation(TypeNode stn, Node t);

  /**
   * @return sygus datatype type to reconstruct equivalent builtin terms into
   */
  TypeNode getType() const;

  /**
   * @return skolem representing this obligation
   */
  Node getSkolem() const;

  /**
   * Add `t` to the set of equivalent builtins this obligation solves.
   *
   * \note `t` MUST be equivalent to the builtin terms in `d_ts`
   *
   * @param t builtin term to add
   */
  void addBuiltin(Node t);

  /**
   * @return equivalent builtin terms to reconstruct for this obligation
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
   * @return set of candidate solutions for this obligation
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
   * @return set of candidate solutions waiting for this obligation to be solved
   */
  const std::unordered_set<Node>& getWatchSet() const;

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
   * Obs = [(k1, {(+ 1 (- x))}, (k2, (- x)), (k3, x), (k4, 0)]
   * CandSols = {k1 -> {(c_+ c_1 k2)}, k2 -> {(c_- k3)},
   *             k3 -> {c_x}, k4 -> {c_0}}
   * root = k1
   *
   * Then, the set of reachable obligations from `root` is {k1, k2, k3}
   *
   * \note requires enabling "sygus-rcons" trace
   *
   * @param root the root obligation to start from
   * @param obs a list of obligations containing at least 1 obligation
   * @param
   */
  static void printCandSols(
      const RConsObligation* root,
      const std::vector<std::unique_ptr<RConsObligation>>& obs);

 private:
  /** Skolem representing this obligation used to embed obligations in candidate
   * solutions. */
  Node d_k;
  /** Equivalent builtin terms for this obligation.
   *
   * To solve the obligation, one of these builtin terms must be reconstructed
   * in the specified grammar (sygus datatype type) of the obligation.
   */
  std::unordered_set<Node> d_ts;
  /** A set of candidate solutions to this obligation.
   *
   * Each candidate solution is a sygus datatype term containing skolem subterms
   * (sub-obligations). By replacing all sub-obligations with their
   * corresponding solutions, we get a term whose builtin analog rewrites to
   * a term in `d_ts` and hence solves this obligation. For example, given:
   *   d_ts = {(+ x y)}
   * a possible set of candidate solutions would be:
   *   d_candSols = {(c_+ k1 k2), (c_+ c_x k2), (c_+ k1 c_y), (c_+ c_x c_y)}
   * where k1 and k2 are skolems. Notice that `d_candSols` may contain a
   * pure term that solves the obligation ((c_+ c_x c_y) in this example).
   */
  std::unordered_set<Node> d_candSols;
  /** A set of candidate solutions waiting for this obligation to be solved.
   *
   * In the example above, (c_+ k1 k2) and (c_+ c_x k2) are in the watch-set of
   * k2. Similarly, (c_+ k1 k2) and (c_+ k1 c_y) are in the watch-set of k1.
   */
  std::unordered_set<Node> d_watchSet;
};

/**
 * Print obligation `ob` into the given output stream `out`
 *
 * @param out the output stream to print `ob` into
 * @param ob the obligation to print
 * @return a reference to the given output stream `out`
 */
std::ostream& operator<<(std::ostream& out, const RConsObligation& ob);

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif  // CVC5__THEORY__QUANTIFIERS__RCONS_OBLIGATION_H
