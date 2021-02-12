/*********************                                                        */
/*! \file rcons_obligation_info.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility class for Sygus Reconstruct module
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__RCONS_OBLIGATION_INFO_H
#define CVC4__THEORY__QUANTIFIERS__RCONS_OBLIGATION_INFO_H

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * A utility class for Sygus Reconstruct obligations. An obligation is a
 * builtin term t and a SyGuS type T, and indicates that we are trying to build
 * a term of type T whose builtin analog is equivalent to t.
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
   * @return builtin term to reconstruct for the corresponding obligation
   */
  Node getBuiltin() const;

  /**
   * Add candidate solution to the set of candidate solutions for the
   * corresponding obligation.
   *
   * @param candSol the candidate solution to add
   */
  void addCandidateSolution(Node candSol);

  /**
   * @return set of candidate solutions for the corresponding obligation
   */
  const std::unordered_set<Node, NodeHashFunction>& getCandidateSolutions()
      const;

  /**
   * Add candidate solution to the set of candidate solutions waiting for the
   * corresponding obligation to be solved.
   *
   * @param candSol the candidate solution to add to watch set
   */
  void addCandidateSolutionToWatchSet(Node candSol);

  /**
   * @return set of candidate solutions waiting for the corresponding obligation
   * to be solved
   */
  const std::unordered_set<Node, NodeHashFunction>& getWatchSet() const;

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
   * \note requires enabling "sygus-rcons" trace
   *
   * @param root The root obligation to start from
   * @param obInfo a map from obligations to their corresponding infos
   */
  static void printCandSols(
      const Node& mainOb,
      const std::unordered_map<Node, RConsObligationInfo, NodeHashFunction>&
          obInfo);

 private:
  /**
   * builtin term for the corresponding obligation. To solve the obligation,
   * this builtin term must be reconstructed in the specified grammar (sygus
   * datatype type).
   */
  Node d_builtin;
  /**
   * a set of candidate solutions to the corresponding obligation. Each
   * candidate solution is a sygus datatype term containing skolem subterms
   * (sub-obligations). By replacing all sub-obligations with their
   * corresponding solution, we get a term whose builtin analog rewrites to
   * `d_builtin` and hence solves this obligation. For example, given:
   * d_builtin = (+ x y)
   * a possible set of candidate solutions would be:
   * d_candSols = {(c_+ c_z1 c_z2), (c_+ c_x c_z2), (c_+ c_z1 c_y),
   *               (c_+ c_x c_y)}
   * where c_z1 and c_z2 are skolems. Notice that `d_candSols` may contain a
   * ground term that solves the obligation ((c_+ c_x c_y) in this example).
   */
  std::unordered_set<Node, NodeHashFunction> d_candSols;
  /**
   * a set of candidate solutions waiting for the corresponding obligation to
   * be solved. In the example above, (c_+ c_z1 c_z2) and (c_+ c_x c_z2) are in
   * the watch-set of c_z2. Similarly, (c_+ c_z1 c_z2) and (c_+ c_z1 c_y) are in
   * the watch-set of c_z1.
   */
  std::unordered_set<Node, NodeHashFunction> d_watchSet;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif  // CVC4__THEORY__QUANTIFIERS__RCONS_OBLIGATION_INFO_H
