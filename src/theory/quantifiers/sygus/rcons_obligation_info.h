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
 * A utility class for Sygus Reconstruct obligations.
 */
class ObligationInfo
{
 public:
  /**
   * Constructor. Default value needed for maps.
   *
   * @param builtin builtin term to reconstruct
   */
  explicit ObligationInfo(const Node& builtin = Node::null());

  /**
   * @return builtin term to reconstruct for the corresponding obligation
   */
  const Node& getBuiltin() const;

  /**
   * Add candidate solution to the set of candidate solutions for the
   * corresponding obligation.
   *
   * @param candSol the candidate solution to add
   */
  void addCandidateSolution(const Node& candSol);

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
  void addCandidateSolutionToWatchSet(const Node& candSol);

  /**
   * @return set of candidate solutions waiting for the corresponding obligation
   * to be solved
   */
  const std::unordered_set<Node, NodeHashFunction>& getWatchSet() const;

 private:
  /** builtin term to reconstruct for the corresponding obligation */
  Node d_builtin;
  /** a set of candidate solutions to the corresponding obligation */
  std::unordered_set<Node, NodeHashFunction> d_candSols;
  /** a set of candidate solutions waiting for the corresponding obligation to
   * be solved */
  std::unordered_set<Node, NodeHashFunction> d_watchSet;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif  // CVC4__THEORY__QUANTIFIERS__RCONS_OBLIGATION_INFO_H
