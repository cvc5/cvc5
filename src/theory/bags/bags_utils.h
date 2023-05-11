/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for bags.
 */

#include <expr/node.h>

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__UTILS_H
#define CVC5__THEORY__BAGS__UTILS_H

#include "theory/theory_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

class BagsUtils
{
 public:
  /**
   * @param bagType type of bags
   * @param bags a vector of bag nodes
   * @return disjoint union of these bags
   */
  static Node computeDisjointUnion(TypeNode bagType,
                                   const std::vector<Node>& bags);
  /**
   * Returns true if n is considered a to be a (canonical) constant bag value.
   * A canonical bag value is one whose AST is:
   *   (bag.union_disjoint (bag e1 c1) ...
   *      (bag.union_disjoint (bag e_{n-1} c_{n-1}) (bag e_n c_n))))
   * where c1 ... cn are positive integers, e1 ... en are constants, and the
   * node identifier of these constants are such that: e1 < ... < en.
   * Also handles the corner cases of empty bag and bag constructed by bag
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
  static Node evaluate(Rewriter* rewriter, TNode n);

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

  /**
   * @param n has the form (bag.fold f t A) where A is a constant bag
   * @return a single value which is the result of the fold
   */
  static Node evaluateBagFold(TNode n);

  /**
   * @param n has the form (bag.partition r A) where A is a constant bag
   * @return a partition of A based on the equivalence relation r
   */
  static Node evaluateBagPartition(Rewriter* rewriter, TNode n);

  /**
   * @param n has the form ((_ table.aggr n1 ... n_k) f initial A)
   * where initial and A are constants
   * @return the aggregation result.
   */
  static Node evaluateTableAggregate(Rewriter* rewriter, TNode n);

  /**
   * @param n has the form (bag.filter p A) where A is a constant bag
   * @return A filtered with predicate p
   */
  static Node evaluateBagFilter(TNode n);

  /**
   * @param n of the form (table.product A B) where A , B of types (Bag T1),
   * (Bag T2) respectively.
   * @param e1 a tuple of type T1 of the form (tuple a1 ... an)
   * @param e2 a tuple of type T2 of the form (tuple b1 ... bn)
   * @return  (tuple a1 ... an b1 ... bn)
   */
  static Node constructProductTuple(TNode n, TNode e1, TNode e2);

  /**
   * @param n of the form (table.product A B) where A, B are constants
   * @return the evaluation of the cross product of A B
   */
  static Node evaluateProduct(TNode n);

  /**
   * @param n of the form ((_ table.join (m_1 n_1 ... m_k n_k) ) A B) where
   * A, B are constants
   * @return the evaluation of inner joining tables A B on columns (m_1, n_1,
   * ..., m_k, n_k)
   */
  static Node evaluateJoin(Rewriter* rewriter, TNode n);

  /**
   * @param n of the form ((_ table.group (n_1 ... n_k) ) A) where A is a
   * constant table
   * @return a partition of A such that each part contains tuples with the same
   * projection with indices n_1 ... n_k
   */
  static Node evaluateGroup(TNode n);

  /**
   * @param n of the form ((_ table.project i_1 ... i_n) A) where A is a
   * constant
   * @return the evaluation of the projection
   */
  static Node evaluateTableProject(TNode n);

  /**
   * @param n has the form ((_ table.join m1 n1 ... mk nk) A B)) where A, B are
   * tables and m1 n1 ... mk nk are indices
   * @return the pair <[m1 ... mk], [n1 ... nk]>
   */
  static std::pair<std::vector<uint32_t>, std::vector<uint32_t>>
  splitTableJoinIndices(Node n);

 private:
  /**
   * a high order helper function that return a constant bag that is the result
   * of (op A B) where op is a binary operator and A, B are constant bags.
   * The result is computed from the elements of A (elementsA with iterator itA)
   * and elements of B (elementsB with iterator itB).
   * The arguments below specify how these iterators are used to generate the
   * elements of the result (elements).
   * @param n a node whose kind is a binary operator (bag.union_disjoint,
   * union_max, intersection_min, difference_subtract, difference_remove) and
   * whose children are constant bags.
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
   * - (bag a 0) = (as bag.empty T) where T is the type of the original bag
   * - (bag a (-c)) = (as bag.empty T) where T is the type the original bag,
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
   * @param n has the form (bag.duplicate_removal A) where A is a constant bag
   * @return a constant bag constructed from the elements in A where each
   * element has multiplicity one
   */
  static Node evaluateDuplicateRemoval(TNode n);

  /**
   * evaluates union disjoint node such that the returned node is a canonical
   * bag that has the form
   * (bag.union_disjoint (bag e1 c1) ...
   *   (bag.union_disjoint  * (bag e_{n-1} c_{n-1}) (bag e_n c_n)))) where
   *   c1... cn are positive integers, e1 ... en are constants, and the node
   * identifier of these constants are such that: e1 < ... < en.
   * @param n has the form (bag.union_disjoint A B) where A, B are constant bags
   * @return the union disjoint of A and B
   */
  static Node evaluateUnionDisjoint(TNode n);
  /**
   * @param n has the form (bag.union_max A B) where A, B are constant bags
   * @return the union max of A and B
   */
  static Node evaluateUnionMax(TNode n);
  /**
   * @param n has the form (bag.inter_min A B) where A, B are constant bags
   * @return the intersection min of A and B
   */
  static Node evaluateIntersectionMin(TNode n);
  /**
   * @param n has the form (bag.difference_subtract A B) where A, B are constant
   * bags
   * @return the difference subtract of A and B
   */
  static Node evaluateDifferenceSubtract(TNode n);
  /**
   * @param n has the form (bag.difference_remove A B) where A, B are constant
   * bags
   * @return the difference remove of A and B
   */
  static Node evaluateDifferenceRemove(TNode n);
  /**
   * @param n has the form (bag.choose A) where A is a constant bag
   * @return x if n has the form (bag.choose (bag x c)). Otherwise an error is
   * thrown.
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
  /**
   * @param n has the form (bag.map f A) where A is a constant bag
   * @return a constant bag constructed from the images of elements in A.
   */
  static Node evaluateBagMap(TNode n);
};
}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__UTILS_H */
