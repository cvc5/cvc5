/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inference generator utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__INFERENCE_GENERATOR_H
#define CVC5__THEORY__BAGS__INFERENCE_GENERATOR_H

#include "expr/node.h"
#include "infer_info.h"

namespace cvc5 {
namespace theory {
namespace bags {

class InferenceManager;
class SolverState;

/**
 * An inference generator class. This class is used by the core solver to
 * generate lemmas
 */
class InferenceGenerator
{
 public:
  InferenceGenerator(SolverState* state, InferenceManager* im);

  /**
   * @param A is a bag of type (Bag E)
   * @param e is a node of type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (>= (bag.count e A) 0)
   */
  InferInfo nonNegativeCount(Node n, Node e);

  /**
   * @param n is (bag x c) of type (Bag E)
   * @param e is a node of type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (= (bag.count e skolem) c))
   *   if e is exactly node x. Node skolem is a fresh variable equals (bag x c).
   *   Otherwise the following inference is returned
   * (=>
   *   true
   *   (= (bag.count e skolem) (ite (= e x) c 0)))
   */
  InferInfo mkBag(Node n, Node e);
  /**
   * @param n is (= A B) where A, B are bags of type (Bag E), and
   * (not (= A B)) is an assertion in the equality engine
   * @return an inference that represents the following implication
   * (=>
   *   (not (= A B))
   *   (not (= (count e A) (count e B))))
   *   where e is a fresh skolem of type E.
   */
  InferInfo bagDisequality(Node n);
  /**
   * @param n is (as emptybag (Bag E))
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (= 0 (count e skolem)))
   *   where skolem = (as emptybag (Bag String))
   */
  InferInfo empty(Node n, Node e);
  /**
   * @param n is (union_disjoint A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (= (count e skolem)
   *      (+ (count e A) (count e B))))
   *  where skolem is a fresh variable equals (union_disjoint A B)
   */
  InferInfo unionDisjoint(Node n, Node e);
  /**
   * @param n is (union_disjoint A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (=
   *     (count e skolem)
   *     (ite
   *       (> (count e A) (count e B))
   *       (count e A)
   *       (count e B)))))
   * where skolem is a fresh variable equals (union_max A B)
   */
  InferInfo unionMax(Node n, Node e);
  /**
   * @param n is (intersection_min A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (=
   *     (count e skolem)
   *     (ite(
   *       (< (count e A) (count e B))
   *       (count e A)
   *       (count e B)))))
   * where skolem is a fresh variable equals (intersection_min A B)
   */
  InferInfo intersection(Node n, Node e);
  /**
   * @param n is (difference_subtract A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (=
   *     (count e skolem)
   *     (ite
   *       (>= (count e A) (count e B))
   *       (- (count e A) (count e B))
   *       0))))
   * where skolem is a fresh variable equals (difference_subtract A B)
   */
  InferInfo differenceSubtract(Node n, Node e);
  /**
   * @param n is (difference_remove A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (=
   *     (count e skolem)
   *     (ite
   *       (= (count e B) 0)
   *       (count e A)
   *       0))))
   * where skolem is a fresh variable equals (difference_remove A B)
   */
  InferInfo differenceRemove(Node n, Node e);
  /**
   * @param n is (duplicate_removal A) where A is a bag of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (=
   *    (count e skolem)
   *    (ite (>= (count e A) 1) 1 0))))
   * where skolem is a fresh variable equals (duplicate_removal A)
   */
  InferInfo duplicateRemoval(Node n, Node e);
  /**
   * @param n is (bag.map f A) where f is a function (-> E T), A a bag of type
   * (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (and
   *   (= (sum 0) 0)
   *   (= (sum preImageSize) (bag.count e skolem))
   *   (>= preImageSize 0)
   *   (forall ((i Int))
   *          (let ((uf_i (uf i)))
   *            (let ((count_uf_i (bag.count uf_i A)))
   *              (=>
   *               (and (>= i 1) (<= i preImageSize))
   *               (and
   *                 (= (f uf_i) e)
   *                 (>= count_uf_i 1)
   *                 (= (sum i) (+ (sum (- i 1)) count_uf_i))
   *                 (forall ((j Int))
   *                   (or
   *                     (not (and (< i j) (<= j preImageSize)))
   *                     (not (= (uf i) (uf j)))) )
   *                 ))))))
   * where uf: Int -> E is an uninterpreted function from integers to the
   * type of the elements of A
   * preImageSize is the cardinality of the distinct elements in A that are
   * mapped to e by function f (i.e., preimage of {e})
   * sum: Int -> Int is a function that aggregates the multiplicities of the
   * preimage of e,
   * and skolem is a fresh variable equals (bag.map f A))
   */
  std::tuple<InferInfo, Node, Node> mapDownwards(Node n, Node e);

  /**
   * @param n is (bag.map f A) where f is a function (-> E T), A a bag of type
   * (Bag E)
   * @param uf is an uninterpreted function Int -> E
   * @param preImageSize is the cardinality of the distinct elements in A that
   * are mapped to y by function f (i.e., preimage of {y})
   * @param y is an element of type T
   * @param e is an element of type E
   * @return an inference that represents the following implication
   * (=>
   *   (>= (bag.count x A) 1)
   *   (or
   *     (not (= (f x) y)
   *     (and
   *       (>= skolem 1)
   *       (<= skolem preImageSize)
   *       (= (uf skolem) x)))))
   * where skolem is a fresh variable
   */
  InferInfo mapUpwards(Node n, Node uf, Node preImageSize, Node y, Node x);

  /**
   * @param element of type T
   * @param bag of type (bag T)
   * @return  a count term (bag.count element bag)
   */
  Node getMultiplicityTerm(Node element, Node bag);

 private:
  /** generate skolem variable for node n and add it to inferInfo */
  Node getSkolem(Node& n, InferInfo& inferInfo);

  NodeManager* d_nm;
  SkolemManager* d_sm;
  SolverState* d_state;
  /** Pointer to the inference manager */
  InferenceManager* d_im;
  /** Commonly used constants */
  Node d_true;
  Node d_zero;
  Node d_one;
};

}  // namespace bags
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BAGS__INFERENCE_GENERATOR_H */
