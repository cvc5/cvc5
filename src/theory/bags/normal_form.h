/*********************                                                        */
/*! \file normal_form.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Normal form for bag constants.
 **/

#include <expr/node.h>

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__NORMAL_FORM_H
#define CVC4__THEORY__BAGS__NORMAL_FORM_H

namespace CVC4 {
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
   * Also handles the corner cases of empty bag and bag constructed from mkBag
   */
  static bool checkNormalConstant(TNode n);
  /**
   * check whether all children of the given node are in normal form
   */
  static bool areChildrenConstants(TNode n);
  /**
   * evaluate the node n to a constant value
   */
  static Node evaluate(TNode n);

 private:
  static std::map<Node, Rational> getBagElements(TNode n);
  static Node constructBagFromElements(TypeNode t,
                                       const std::map<Node, Rational>& map);
  template <typename T1, typename T2, typename T3, typename T4, typename T5>
  static Node evaluateBinaryOperation(const TNode& n,
                                      T1&& lambda,
                                      T2&& lessLambda,
                                      T3&& geqLambda,
                                      T4&& remainingA,
                                      T5&& remainingB);
  /**
   * evaluate n as follows:
   * - (mkBag a 0) = (emptybag T) where T is the type of a
   * - (mkBag a (-c)) = (emptybag T) where T is the type of a, and c > 0 is a
   *   constant
   * - otherwise = n
   */
  static Node evaluateMakeBag(TNode n);

  /**
   * evaluate n as follows:
   * - (bag.count "x" (emptybag String)) = 0
   * - (bag.count "x" (mkBag "y" 5)) = 0
   * - (bag.count "x" (mkBag "x" 4)) = 4
   * - (bag.count "x" (union_disjoint (mkBag "x" 4) (mkBag "y" 5)) = 4
   * - (bag.count "x" (union_disjoint (mkBag "y" 5) (mkBag "z" 5)) = 0
   */
  static Node evaluateBagCount(TNode n);

  /**
   * evaluate union disjoint node such that the returned node is a canonical bag
   * that has the form
   * (union_disjoint (mkBag e1 c1) ...
   *    (union_disjoint (mkBag e_{n-1} c_{n-1}) (mkBag e_n c_n))))
   * where c1 ... cn are positive integers, e1 ... en are constants, and the
   * node identifier of these constants are such that: e1 < ... < en.
   */
  static Node evaluateUnionDisjoint(TNode n);
  static Node evaluateUnionMax(TNode n);
  static Node evaluateIntersectionMin(TNode n);
  static Node evaluateDifferenceSubtract(TNode n);
  static Node evaluateDifferenceRemove(TNode n);
  static Node evaluateChoose(TNode n);
  static Node evaluateCard(TNode n);
  static Node evaluateIsSingleton(TNode n);
  static Node evaluateFromSet(TNode n);
  static Node evaluateToSet(TNode n);
};
}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__NORMAL_FORM_H */
