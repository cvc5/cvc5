/*********************                                                        */
/*! \file inference_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Inference generator utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__INFERENCE_GENERATOR_H
#define CVC4__THEORY__BAGS__INFERENCE_GENERATOR_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "infer_info.h"
#include "theory/bags/solver_state.h"

namespace CVC4 {
namespace theory {
namespace bags {

/**
 * An inference generator class. This class is used by the core solver to
 * generate lemmas
 */
class InferenceGenerator
{
 public:
  InferenceGenerator(SolverState* state);

  /**
   * @param n is (bag x c) of type (Bag E)
   * @param e is a node of type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (= (bag.count e (bag x c)) (ite (= e x) c 0)))
   */
  InferInfo mkBag(Node n, Node e);

  /**
   * @param n is (= A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   (= A B)
   *   (= (count e A) (count e B)))
   */
  InferInfo bagEquality(Node n, Node e);
  /**
   * @param n is (not (= A B)) where A, B are bags of type (Bag E)
   * @return an inference that represents the following implication
   * (=>
   *   (not (= A B))
   *   (not (= (count e A) (count e B))))
   *   where e is a fresh skolem of type E
   */
  InferInfo bagDisequality(Node n);
  /**
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (= 0 (count e (as emptybag (Bag E)))))
   */
  InferInfo bagEmpty(Node e);
  /**
   * @param n is (union_disjoint A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (= (count e k_{(union_disjoint A B)})
   *      (+ (count e A) (count e B))))
   *  where k_{(union_disjoint A B)} is a unique purification skolem
   *  for (union_disjoint A B)
   */
  InferInfo unionDisjoint(Node n, Node e);
  /**
   * @param n is (union_disjoint A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (= (count e (union_max A B))
   *     (ite
   *     (> (count e A) (count e B))
   *     (count e A)
   *     (count e B)))))
   */
  InferInfo unionMax(Node n, Node e);
  /**
   * @param n is (intersection_min A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (= (count e (intersection_min A B))
   *     (ite(
   *     (< (count e A) (count e B))
   *     (count e A)
   *     (count e B)))))
   */
  InferInfo intersection(Node n, Node e);
  /**
   * @param n is (difference_subtract A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (= (count e (difference_subtract A B))
   *     (ite
   *        (>= (count e A) (count e B))
   *        (- (count e A) (count e B))
   *        0))))
   */
  InferInfo differenceSubtract(Node n, Node e);
  /**
   * @param n is (difference_remove A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (= (count e (difference_remove A B))
   *     (ite
   *        (= (count e B) 0)
   *        (count e A)
   *        0))))
   */
  InferInfo differenceRemove(Node n, Node e);
  /**
   * @param n is (duplicate_removal A) where A is a bag of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (= (count e (duplicate_removal A))
   *     (ite (>= (count e A) 1) 1 0))))
   */
  InferInfo duplicateRemoval(Node n, Node e);

  /**
   * @param element of type T
   * @param bag of type (bag T)
   * @param inferInfo to store new skolem
   * @return  a skolem for (bag.count element bag)
   */
  Node getMultiplicitySkolem(Node element, Node bag, InferInfo& inferInfo);

 private:
  NodeManager* d_nm;
  SkolemManager* d_sm;
  SolverState* d_state;
  Node d_true;
  Node d_zero;
  Node d_one;
};

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__INFERENCE_GENERATOR_H */
