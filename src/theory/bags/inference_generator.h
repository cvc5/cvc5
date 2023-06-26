/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {
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
   * @param n a node of the form (bag.count e A)
   * this function generates a skolem that equals (bag.count repE repA) where
   * repE, repA are representatives of e, A respectively
   */
  void registerCountTerm(Node n);

  /**
   * @param n a node of the form (bag.card A)
   * @return a skolem that equals (bag.card repA) where repA is the
   * representative of A
   */
  void registerCardinalityTerm(Node n);

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
   * @param n a node of integer type that equals to a card term
   * @return an inference that represents the following implication
   * (>= n 0)
   */
  InferInfo nonNegativeCardinality(Node n);

  /**
   * @param n is (bag x c) of type (Bag E)
   * @return an inference that represents the following lemma:
   * (or
   *   (and (<  c 1) (= (bag x c) (as bag.empty (Bag E))))
   *   (and (>= c 1) (not (= (bag x c) (as bag.empty (Bag E))))
   */
  InferInfo bagMake(Node n);

  /**
   * @param n is (bag x c) of type (Bag E)
   * @param e is a node of type E
   * @return an inference that represents the following lemma:
   * (ite (and (= e x) (>= c 1))
   *   (= (bag.count e skolem) c)
   *   (= (bag.count e skolem) 0))
   * where skolem = (bag x c) is a fresh variable
   */
  InferInfo bagMake(Node n, Node e);
  /**
   * @param equality is (= A B) where A, B are bags of type (Bag E), and
   * (not (= A B)) is an assertion in the equality engine
   * @param witness a skolem node that witnesses the disequality
   * @return an inference that represents the following implication
   * (=>
   *   (not (= A B))
   *   (not (= (bag.count witness A) (bag.count witness B))))
   *   where witness is a skolem of type E.
   */
  InferInfo bagDisequality(Node equality, Node witness);
  /**
   * @param n is (as bag.empty (Bag E))
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (= 0 (bag.count e skolem)))
   *   where skolem = (as bag.empty (Bag E))
   */
  InferInfo empty(Node n, Node e);
  /**
   * @param n is (bag.union_disjoint A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (= (bag.count e skolem)
   *      (+ (bag.count e A) (bag.count e B))))
   *  where skolem is a fresh variable equals (bag.union_disjoint A B)
   */
  InferInfo unionDisjoint(Node n, Node e);
  /**
   * @param n is (bag.union_disjoint A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (=
   *     (bag.count e skolem)
   *     (ite
   *       (> (bag.count e A) (bag.count e B))
   *       (bag.count e A)
   *       (bag.count e B)))))
   * where skolem is a fresh variable equals (bag.union_max A B)
   */
  InferInfo unionMax(Node n, Node e);
  /**
   * @param n is (bag.inter_min A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (=
   *     (bag.count e skolem)
   *     (ite(
   *       (< (bag.count e A) (bag.count e B))
   *       (bag.count e A)
   *       (bag.count e B)))))
   * where skolem is a fresh variable equals (bag.inter_min A B)
   */
  InferInfo intersection(Node n, Node e);
  /**
   * @param n is (bag.difference_subtract A B) where A, B are bags of type
   * (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (=
   *     (bag.count e skolem)
   *     (ite
   *       (>= (bag.count e A) (bag.count e B))
   *       (- (bag.count e A) (bag.count e B))
   *       0))))
   * where skolem is a fresh variable equals (bag.difference_subtract A B)
   */
  InferInfo differenceSubtract(Node n, Node e);
  /**
   * @param n is (bag.difference_remove A B) where A, B are bags of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (=
   *     (bag.count e skolem)
   *     (ite
   *       (<= (bag.count e B) 0)
   *       (bag.count e A)
   *       0))))
   * where skolem is a fresh variable equals (bag.difference_remove A B)
   */
  InferInfo differenceRemove(Node n, Node e);
  /**
   * @param n is (bag.duplicate_removal A) where A is a bag of type (Bag E)
   * @param e is a node of Type E
   * @return an inference that represents the following implication
   * (=>
   *   true
   *   (=
   *    (bag.count e skolem)
   *    (ite (>= (bag.count e A) 1) 1 0))))
   * where skolem is a fresh variable equals (bag.duplicate_removal A)
   */
  InferInfo duplicateRemoval(Node n, Node e);
  /**
   * @param cardTerm a term of the form (bag.card A) where A has type (Bag E)
   * @param n is (as bag.empty (Bag E))
   * @return an inference that represents the following implication
   * (= (= A (as bag.empty (Bag E)))
   *     (= (bag.card A) 0))
   */
  InferInfo cardEmpty(const std::pair<Node, Node>& pair, Node n);
  /**
   * @param cardTerm a term of the form (bag.card A) where A has type (Bag E)
   * @param n is a node of the form (bag x c) of type (Bag E)
   * @return an inference that represents the following implication
   * (=>
   *     (and (= A (bag x c)) (>= 0 c))
   *     (= (bag.card A) c))
   */
  InferInfo cardBagMake(const std::pair<Node, Node>& pair, Node n);
  /**
   * @param premise a boolean node explains why parent equals the disjoint union
   * of its children
   * @param parent a bag term
   * @param children (child_1, ... child_n) nonempty set of bag terms
   * @return an inference that represents the following implication
   * (=> premise
   *     (and
   *       (= parent (bag.union_disjoint child_1 ... child_n))
   *       (= (bag.card parent) (+ (bag.card child_1) ... (bag.card child_n)))))
   */
  InferInfo cardUnionDisjoint(Node premise,
                              Node parent,
                              const std::set<Node>& children);

  /**
   * @param n is (bag.map f A) where f is a function (-> E T), A a bag of type
   * (Bag E)
   * @param e is a node of Type T
   * @return an inference that represents the following implication
   * (and
   *   (= (sum 0) 0)
   *   (= (sum preImageSize) (bag.count e skolem))
   *   (>= preImageSize 0)
   *   (forall ((i Int))
   *          (let ((uf_i (uf i)))
   *            (let ((bag.count_uf_i (bag.count uf_i A)))
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
  std::tuple<InferInfo, Node, Node> mapDown(Node n, Node e);

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
   *   (bag.member x A)
   *   (or
   *     (not (= (f x) y)
   *     (and
   *       (>= skolem 1)
   *       (<= skolem preImageSize)
   *       (= (uf skolem) x)))))
   * where skolem is a fresh variable
   */
  InferInfo mapUp(Node n, Node uf, Node preImageSize, Node y, Node x);

  /**
   * @param n is (bag.filter p A) where p is a function (-> E Bool),
   * A a bag of type (Bag E)
   * @param e is an element of type E
   * @return an inference that represents the following implication
   * (=>
   *   (bag.member e skolem)
   *   (and
   *     (p e)
   *     (= (bag.count e skolem) (bag.count e A)))
   * where skolem is a variable equals (bag.filter p A)
   */
  InferInfo filterDown(Node n, Node e);

  /**
   * @param n is (bag.filter p A) where p is a function (-> E Bool),
   * A a bag of type (Bag E)
   * @param e is an element of type E
   * @return an inference that represents the following implication
   * (=>
   *   (bag.member e A)
   *   (or
   *     (and (p e) (= (bag.count e skolem) (bag.count A)))
   *     (and (not (p e)) (= (bag.count e skolem) 0)))
   * where skolem is a variable equals (bag.filter p A)
   */
  InferInfo filterUp(Node n, Node e);

  /**
   * @param n is a (table.product A B) where A, B are tables
   * @param e1 an element of the form (tuple a1 ... am)
   * @param e2 an element of the form (tuple b1 ... bn)
   * @return  an inference that represents the following
   * (=> (and (bag.member e1 A) (bag.member e2 B))
   *     (=
   *       (bag.count (tuple a1 ... am b1 ... bn) skolem)
   *       (* (bag.count e1 A) (bag.count e2 B))))
   * where skolem is a variable equals (bag.product A B)
   */
  InferInfo productUp(Node n, Node e1, Node e2);

  /**
   * @param n is a (table.product A B) where A, B are tables
   * @param e an element of the form (tuple a1 ... am b1 ... bn)
   * @return an inference that represents the following
   * (=> (bag.member e skolem)
   *   (=
   *     (bag.count (tuple a1 ... am b1 ... bn) skolem)
   *     (* (bag.count (tuple a1 ... am A) (bag.count (tuple b1 ... bn) B))))
   * where skolem is a variable equals (bag.product A B)
   */
  InferInfo productDown(Node n, Node e);

  /**
   * @param n is a ((_ table.join m1 n1 ... mk nk) A B) where A, B are tables
   * @param e1 an element of the form (tuple a1 ... am)
   * @param e2 an element of the form (tuple b1 ... bn)
   * @return  an inference that represents the following
   * (=> (and
   *       (bag.member e1 A)
   *       (bag.member e2 B)
   *       (= a_{m1} b_{n1}) ... (= a_{mk} b_{nk}))
   *     (=
   *       (bag.count (tuple a1 ... am b1 ... bn) skolem)
   *       (* (bag.count e1 A) (bag.count e2 B))))
   * where skolem is a variable equals ((_ table.join m1 n1 ... mk nk) A B)
   */
  InferInfo joinUp(Node n, Node e1, Node e2);

  /**
   * @param n is a (table.product A B) where A, B are tables
   * @param e an element of the form (tuple a1 ... am b1 ... bn)
   * @return an inference that represents the following
   * (=> (bag.member e skolem)
   *   (and
   *     (= a_{m1} b_{n1}) ... (= a_{mk} b_{nk})
   *     (=
   *       (bag.count (tuple a1 ... am b1 ... bn) skolem)
   *       (* (bag.count (tuple a1 ... am A) (bag.count (tuple b1 ... bn) B))))
   * where skolem is a variable equals ((_ table.join m1 n1 ... mk nk) A B)
   */
  InferInfo joinDown(Node n, Node e);

  /**
   * @param element of type T
   * @param bag of type (bag T)
   * @return  a count term (bag.count element bag)
   */
  Node getMultiplicityTerm(Node element, Node bag);

  /**
   * @param n has form ((_ table.group n1 ... nk) A) where A has type T
   * @return an inference that represents:
   * (=>
   *  (= A (as bag.empty T))
   *  (= skolem (bag (as bag.empty T) 1))
   * )
   * where skolem is a variable equals ((_ table.group n1 ... nk) A)
   */
  InferInfo groupNotEmpty(Node n);
  /**
   * @param n has form ((_ table.group n1 ... nk) A) where A has type (Table T)
   * @param e an element of type T
   * @param part a skolem function of type T -> (Table T) created uniquely for n
   * by defineSkolemPartFunction function below
   * @return an inference that represents:
   * (=>
   *   (bag.member x A)
   *   (and
   *     (= (bag.count (part x) skolem) 1)
   *     (= (bag.count x (part x)) (bag.count x A))
   *     (= (bag.count (as bag.empty (Table T)) skolem) 0)
   *   )
   * )
   *
   * where skolem is a variable equals ((_ table.group n1 ... nk) A)
   */
  InferInfo groupUp1(Node n, Node x, Node part);
  /**
   * @param n has form ((_ table.group n1 ... nk) A) where A has type (Table T)
   * @param e an element of type T
   * @param part a skolem function of type T -> (Table T) created uniquely for n
   * by defineSkolemPartFunction function below
   * @return an inference that represents:
   * (=>
   *   (= (bag.count x A) 0)
   *   (= (part x) (as bag.empty (Table T)))
   * )
   * where skolem is a variable equals ((_ table.group n1 ... nk) A)
   */
  InferInfo groupUp2(Node n, Node x, Node part);
  /**
   * @param n has form ((_ table.group n1 ... nk) A) where A has type (Table T)
   * @param B an element of type (Table T)
   * @param x an element of type T
   * @param part a skolem function of type T -> (Table T) created uniquely for n
   * by defineSkolemPartFunction function below
   * @return an inference that represents:
   * (=>
   *   (and
   *     (bag.member B skolem)
   *     (bag.member x B)
   *   )
   *   (and
   *     (= (bag.count x B) (bag.count x A))
   *     (= (part x) B)
   *   )
   * )
   * where skolem is a variable equals ((_ table.group n1 ... nk) A).
   */
  InferInfo groupDown(Node n, Node B, Node x, Node part);
  /**
   * @param n has form ((_ table.group n1 ... nk) A) where A has type (Table T)
   * @param B an element of type (Table T) and B is not of the form (part x)
   * @param part a skolem function of type T -> (Table T) created uniquely for n
   * by defineSkolemPartFunction function below
   * @return an inference that represents:
   * (=>
   *   (and
   *     (bag.member B skolem)
   *     (not (= A (as bag.empty (Table T)))
   *   )
   *   (and
   *     (= (bag.count B skolem) 1)
   *     (= B (part k_{n, B}))
   *     (>= (bag.count k_{n,B} B) 1)
   *     (= (bag.count k_{n,B} B) (bag.count k_{n,B} A))
   *   )
   * )
   * where skolem is a variable equals ((_ table.group n1 ... nk) A), and
   * k_{n, B} is a fresh skolem of type T.
   */
  InferInfo groupPartCount(Node n, Node B, Node part);
  /**
   * @param n has form ((_ table.group n1 ... nk) A) where A has type (Table T)
   * @param B an element of type (Table T)
   * @param x an element of type T
   * @param y an element of type T
   * @param part a skolem function of type T -> (Table T) created uniquely for n
   * by defineSkolemPartFunction function below
   * @return an inference that represents:
   * (=>
   *   (and
   *     (bag.member B skolem)
   *     (bag.member x B)
   *     (bag.member y B)
   *     (distinct x y)
   *   )
   *   (and
   *     (= ((_ tuple.project n1 ... nk) x)
   *        ((_ tuple.project n1 ... nk) y))
   *     (= (part x) (part y))
   *     (= (part x) B)
   *   )
   * )
   * where skolem is a variable equals ((_ table.group n1 ... nk) A).
   */
  InferInfo groupSameProjection(Node n, Node B, Node x, Node y, Node part);
  /**
   * @param n has form ((_ table.group n1 ... nk) A) where A has type (Table T)
   * @param B an element of type (Table T)
   * @param x an element of type T
   * @param y an element of type T
   * @param part a skolem function of type T -> (Table T) created uniquely for n
   * by defineSkolemPartFunction function below
   * @return an inference that represents:
   * (=>
   *   (and
   *     (bag.member B skolem)
   *     (bag.member x B)
   *     (bag.member y A)
   *     (distinct x y)
   *     (= ((_ tuple.project n1 ... nk) x)
   *        ((_ tuple.project n1 ... nk) y))
   *   )
   *   (and
   *     (= (bag.count y B) (bag.count y A))
   *     (= (part x) (part y))
   *     (= (part x) B)
   *   )
   * )
   * where skolem is a variable equals ((_ table.group n1 ... nk) A).
   */
  InferInfo groupSamePart(Node n, Node B, Node x, Node y, Node part);
  /**
   * @param n has form ((_ table.group n1 ... nk) A) where A has type (Table T)
   * @return a function of type T -> (Table T) that maps elements T to a part in
   * the partition
   */
  Node defineSkolemPartFunction(Node n);

 private:
  /**
   * generate skolem variable for node n and add pending lemma for the equality
   */
  Node registerAndAssertSkolemLemma(Node& n);

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
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__INFERENCE_GENERATOR_H */
