/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {
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

  /** clear all data structures */
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
  /**
   * This function propagates minsize constraints for a leaf bag and related
   * elements.
   * Example If bag A is a leaf and {e1, ... , en} are elements, then this
   * function adds the following lemmas:
   * - (<= (bag.count e1 A) (bag.card A))
   * - (<= (bag.count e2 A) (bag.card A))
   *   ...
   * - (<= (bag.count en A) (bag.card A))
   *   (=> (distinct e1 e2)
   *       (<= (+ (bag.count e1 A) (bag.count e2 A))
   *           (bag.card A)))
   *
   * - (=> (distinct e1 e2 e3)
   *      (<= (+ (bag.count e1 A) (bag.count e2 A) (bag.count e3 A))
   *          (bag.card A)))
   *   ...
   * - (=> (distinct e1 ... en)
   *     (<= (+ (bag.count e1 A) ... (bag.count en A))
   *         (bag.card A)))
   */
  void checkLeafBag(const std::pair<Node, Node>& pair, const Node& bag);
  /**
   * This function updates cardinality graph by adding parent and its children
   * to the cardinality graph. It also adds necessary lemmas when the premise
   * holds.
   * @param premise a node of boolean type
   * @param parent a representative bag term
   * @param children a set of bag representatives whose disjoint union equals to
   * parent when the premise holds
   */
  void addChildren(const Node& premise,
                   const Node& parent,
                   const std::set<Node>& children);

  /** The solver state object */
  SolverState& d_state;
  /** The inference generator object*/
  InferenceGenerator d_ig;
  /** Reference to the inference manager for the theory of bags */
  InferenceManager& d_im;
  NodeManager* d_nm;

  /**
   * A map from bag representatives to sets of bag representatives with the
   * invariant that each key is the disjoint union of each set in the value.
   * Example:
   * C -> {{A, B}, {X,Y, Z}}
   * implies we have the following constraints in the current context.
   * (= C (bag.union_disjoint A B))
   * (= C (bag.union_disjoint X Y Z))
   * This map needs to cleared before each full effort check.
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
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__CARD__SOLVER_H */
