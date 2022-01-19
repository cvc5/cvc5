/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Cardinality solver for theory of bags.
 */

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "cvc5_private.h"
#include "smt/env_obj.h"
#include "theory/bags/bag_reduction.h"

#ifndef CVC5__THEORY__CARD__SOLVER_H
#define CVC5__THEORY__CARD__SOLVER_H

#include "theory/bags/inference_generator.h"

namespace cvc5 {
namespace theory {
namespace bags {

class InferenceManager;
class SolverState;
class TermRegistry;

/** The cardinality solver for the theory of bags
 *
 */
class CardSolver : protected EnvObj
{
 public:
  CardSolver(Env& env, SolverState& s, InferenceManager& im);
  ~CardSolver();

  void reset();

  /**
   * add lemmas related to cardinality constraints
   */
  void checkCardinalityGraph();
  /**
   * @param bag a node of a bag type
   * @return whether the given node is a leaf in the cardinality graph
   */
  bool isLeaf(const Node& bag);

  /**
   * @param bag a node of a bag type
   * @return a set of children for that bag in the cardinality graph
   */
  std::set<Node> getChildren(Node bag);

 private:
  /**
   * Generate all cardinality terms needed in the cardinality graph.
   * Example:
   * If (bag.card B) is a term, and (bag.union_max A B) is a term, then
   * the following cardinality terms would be added:
   *  (bag.card (bag.union_max A B))
   *  (bag.card A)
   *  (bag.card (bag.inter_min A B))
   */
  void generateRelatedCardinalityTerms();

  /** apply inference rules for empty bags */
  void checkEmpty(const std::pair<Node, Node>& pair, const Node& n);
  /** apply inference rules for bag make */
  void checkBagMake(const std::pair<Node, Node>& pair, const Node& n);
  /** apply inference rules for union disjoint */
  void checkUnionDisjoint(const std::pair<Node, Node>& pair, const Node& n);
  /** apply inference rules for union max */
  void checkUnionMax(const std::pair<Node, Node>& pair, const Node& n);
  /** apply inference rules for intersection_min operator */
  void checkIntersectionMin(const std::pair<Node, Node>& pair, const Node& n);
  /** apply inference rules for difference subtract */
  void checkDifferenceSubtract(const std::pair<Node, Node>& pair,
                               const Node& n);
  /** apply inference rules for difference remove */
  void checkDifferenceRemove(const std::pair<Node, Node>& pair, const Node& n);
  /** apply inference rules for leaves in the cardinality graph
   *
   */
  void checkLeafBag(const std::pair<Node, Node>& pair, const Node& bag);
  void addChildren(const Node& parent, const std::set<Node>& children);
  void mergeChildren(const std::set<Node>& set1, const std::set<Node>& set2);
  std::set<Node> getLeaves(const std::set<Node>& set);
  /** The solver state object */
  SolverState& d_state;
  /** The inference generator object*/
  InferenceGenerator d_ig;
  /** Reference to the inference manager for the theory of bags */
  InferenceManager& d_im;
  NodeManager* d_nm;

  /** bag reduction */
  BagReduction d_bagReduction;

  /**
   * A map from bags to sets of bags with the invariant that each key bag is the
   * disjoint union of each set in the value.
   * Example:
   * C -> {{A, B}, {X,Y, Z}}
   * implies we have the constraints
   * (= C (bag.union_disjoint A B))
   * (= C (bag.union_disjoint X Y Z))
   */
  std::map<Node, std::set<std::set<Node>>> d_cardGraph;

  /** Commonly used constants */
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
}; /* class CardSolver */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__CARD__SOLVER_H */
