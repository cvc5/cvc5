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
 * Normal form for bag constants.
 */

#include <expr/node.h>

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__NORMAL_FORM_H
#define CVC5__THEORY__BAGS__NORMAL_FORM_H

namespace cvc5 {
namespace theory {
namespace bags {

class NormalForm
{
 public:
  /**
   * Returns true if n is considered a to be a (canonical) constant bag value.
   * A canonical bag value is one whose AST is:
   *   (union_disjoint (mkBag e1 c1) ...
   *      (union_disjoint (mkBag e_{n-1} c_{n-1}) (mkBag e_n c_n))))
   * where c1 ... cn are positive integers, e1 ... en are constants, and the
   * node identifier of these constants are such that: e1 < ... < en.
   * Also handles the corner cases of empty bag and bag constructed by mkBag
   */
  static bool isConstant(TNode n);
  /**
   * check whether all children of the given node are constants
   */
  static bool areChildrenConstants(TNode n);
  /**
   * evaluate the node n to a constant value.
   * As a precondition, children of n should be constants.
   */
  static Node evaluate(TNode n);

  /**
   * get the elements along with their multiplicities in a given bag
   * @param n a constant node whose type is a bag
   * @return a map whose keys are constant elements and values are
   * multiplicities
   */
  static std::map<Node, Rational> getBagElements(TNode n);

  /**
   * construct a constant bag from constant elements
   * @param t the type of the returned bag
   * @param elements a map whose keys are constant elements and values are
   *        multiplicities
   * @return a constant bag that contains
   */
  static Node constructConstantBagFromElements(
      TypeNode t, const std::map<Node, Rational>& elements);

  /**
   * construct a constant bag from node elements
   * @param t the type of the returned bag
   * @param elements a map whose keys are constant elements and values are
   *        multiplicities
   * @return a constant bag that contains
   */
  static Node constructBagFromElements(TypeNode t,
                                       const std::map<Node, Node>& elements);

 private:
  /**
   * a high order helper function that return a constant bag that is the result
   * of (op A B) where op is a binary operator and A, B are constant bags.
   * The result is computed from the elements of A (elementsA with iterator itA)
   * and elements of B (elementsB with iterator itB).
   * The arguments below specify how these iterators are used to generate the
   * elements of the result (elements).
   * @param n a node whose kind is a binary operator (union_disjoint, union_max,
   * intersection_min, difference_subtract, difference_remove) and whose
   * children are constant bags.
   * @param equal a lambda expression that receives (elements, itA, itB) and
   * specify the action that needs to be taken when the elements of itA, itB are
   * equal.
   * @param less a lambda expression that receives (elements, itA, itB) and
   * specify the action that needs to be taken when the element itA is less than
   * the element of itB.
   * @param greaterOrEqual less a lambda expression that receives (elements,
   * itA, itB) and specify the action that needs to be taken when the element
   * itA is greater than or equal than the element of itB.
   * @param remainderOfA a lambda expression that receives (elements, elementsA,
   * itA) and specify the action that needs to be taken to the remaining
   * elements of A when all elements of B are visited.
   * @param remainderOfB a lambda expression that receives (elements, elementsB,
   * itB) and specify the action that needs to be taken to the remaining
   * elements of B when all elements of A are visited.
   * @return a constant bag that the result of (op n[0] n[1])
   */
  template <typename T1, typename T2, typename T3, typename T4, typename T5>
  static Node evaluateBinaryOperation(const TNode& n,
                                      T1&& equal,
                                      T2&& less,
                                      T3&& greaterOrEqual,
                                      T4&& remainderOfA,
                                      T5&& remainderOfB);
  /**
   * evaluate n as follows:
   * - (mkBag a 0) = (emptybag T) where T is the type of the original bag
   * - (mkBag a (-c)) = (emptybag T) where T is the type the original bag,
   *                                and c > 0 is a constant
   */
  static Node evaluateMakeBag(TNode n);

  /**
   * returns the multiplicity in a constant bag
   * @param n has the form (bag.count x A) where x, A are constants
   * @return the multiplicity of element x in bag A.
   */
  static Node evaluateBagCount(TNode n);

  /**
   * @param n has the form (duplicate_removal A) where A is a constant bag
   * @return a constant bag constructed from the elements in A where each
   * element has multiplicity one
   */
  static Node evaluateDuplicateRemoval(TNode n);

  /**
   * evaluates union disjoint node such that the returned node is a canonical
   * bag that has the form
   * (union_disjoint (mkBag e1 c1) ...
   *   (union_disjoint  * (mkBag e_{n-1} c_{n-1}) (mkBag e_n c_n)))) where
   *   c1... cn are positive integers, e1 ... en are constants, and the node
   * identifier of these constants are such that: e1 < ... < en.
   * @param n has the form (union_disjoint A B) where A, B are constant bags
   * @return the union disjoint of A and B
   */
  static Node evaluateUnionDisjoint(TNode n);
  /**
   * @param n has the form (union_max A B) where A, B are constant bags
   * @return the union max of A and B
   */
  static Node evaluateUnionMax(TNode n);
  /**
   * @param n has the form (intersection_min A B) where A, B are constant bags
   * @return the intersection min of A and B
   */
  static Node evaluateIntersectionMin(TNode n);
  /**
   * @param n has the form (difference_subtract A B) where A, B are constant
   * bags
   * @return the difference subtract of A and B
   */
  static Node evaluateDifferenceSubtract(TNode n);
  /**
   * @param n has the form (difference_remove A B) where A, B are constant bags
   * @return the difference remove of A and B
   */
  static Node evaluateDifferenceRemove(TNode n);
  /**
   * @param n has the form (bag.choose A) where A is a constant bag
   * @return the first element of A if A is not empty. Otherwise, it returns the
   * first element returned by the type enumerator for the elements
   */
  static Node evaluateChoose(TNode n);
  /**
   * @param n has the form (bag.card A) where A is a constant bag
   * @return the number of elements in bag A
   */
  static Node evaluateCard(TNode n);
  /**
   * @param n has the form (bag.is_singleton A) where A is a constant bag
   * @return whether the bag A has cardinality one.
   */
  static Node evaluateIsSingleton(TNode n);
  /**
   * @param n has the form (bag.from_set A) where A is a constant set
   * @return a constant bag that contains exactly the elements in A.
   */
  static Node evaluateFromSet(TNode n);
  /**
   * @param n has the form (bag.to_set A) where A is a constant bag
   * @return a constant set constructed from the elements in A.
   */
  static Node evaluateToSet(TNode n);
};
}  // namespace bags
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BAGS__NORMAL_FORM_H */
