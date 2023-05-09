/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Mathias Preiner
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
#include "bags_utils.h"

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/emptybag.h"
#include "smt/logic_exception.h"
#include "theory/bags/bag_reduction.h"
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/rewriter.h"
#include "theory/sets/normal_form.h"
#include "theory/type_enumerator.h"
#include "theory/uf/equality_engine.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory::datatypes;

namespace cvc5::internal {
namespace theory {
namespace bags {

Node BagsUtils::computeDisjointUnion(TypeNode bagType,
                                     const std::vector<Node>& bags)
{
  NodeManager* nm = NodeManager::currentNM();
  if (bags.empty())
  {
    return nm->mkConst(EmptyBag(bagType));
  }
  if (bags.size() == 1)
  {
    return bags[0];
  }
  Node unionDisjoint = bags[0];
  for (size_t i = 1; i < bags.size(); i++)
  {
    if (bags[i].getKind() == BAG_EMPTY)
    {
      continue;
    }
    unionDisjoint = nm->mkNode(BAG_UNION_DISJOINT, unionDisjoint, bags[i]);
  }
  return unionDisjoint;
}

bool BagsUtils::isConstant(TNode n)
{
  if (n.getKind() == BAG_EMPTY)
  {
    // empty bags are already normalized
    return true;
  }
  if (n.getKind() == BAG_MAKE)
  {
    // see the implementation in MkBagTypeRule::computeIsConst
    return n.isConst();
  }
  if (n.getKind() == BAG_UNION_DISJOINT)
  {
    if (!(n[0].getKind() == kind::BAG_MAKE && n[0].isConst()))
    {
      // the first child is not a constant
      return false;
    }
    // store the previous element to check the ordering of elements
    Node previousElement = n[0][0];
    Node current = n[1];
    while (current.getKind() == BAG_UNION_DISJOINT)
    {
      if (!(current[0].getKind() == kind::BAG_MAKE && current[0].isConst()))
      {
        // the current element is not a constant
        return false;
      }
      if (previousElement >= current[0][0])
      {
        // the ordering is violated
        return false;
      }
      previousElement = current[0][0];
      current = current[1];
    }
    // check last element
    if (!(current.getKind() == kind::BAG_MAKE && current.isConst()))
    {
      // the last element is not a constant
      return false;
    }
    if (previousElement >= current[0])
    {
      // the ordering is violated
      return false;
    }
    return true;
  }

  // only nodes with kinds EMPTY_BAG, BAG_MAKE, and BAG_UNION_DISJOINT can be
  // constants
  return false;
}

bool BagsUtils::areChildrenConstants(TNode n)
{
  return std::all_of(n.begin(), n.end(), [](Node c) { return c.isConst(); });
}

Node BagsUtils::evaluate(Rewriter* rewriter, TNode n)
{
  Assert(areChildrenConstants(n));
  if (n.isConst())
  {
    // a constant node is already in a normal form
    return n;
  }
  switch (n.getKind())
  {
    case BAG_MAKE: return evaluateMakeBag(n);
    case BAG_COUNT: return evaluateBagCount(n);
    case BAG_DUPLICATE_REMOVAL: return evaluateDuplicateRemoval(n);
    case BAG_UNION_DISJOINT: return evaluateUnionDisjoint(n);
    case BAG_UNION_MAX: return evaluateUnionMax(n);
    case BAG_INTER_MIN: return evaluateIntersectionMin(n);
    case BAG_DIFFERENCE_SUBTRACT: return evaluateDifferenceSubtract(n);
    case BAG_DIFFERENCE_REMOVE: return evaluateDifferenceRemove(n);
    case BAG_CARD: return evaluateCard(n);
    case BAG_IS_SINGLETON: return evaluateIsSingleton(n);
    case BAG_FROM_SET: return evaluateFromSet(n);
    case BAG_TO_SET: return evaluateToSet(n);
    case BAG_MAP: return evaluateBagMap(n);
    case BAG_FILTER: return evaluateBagFilter(n);
    case BAG_FOLD: return evaluateBagFold(n);
    case TABLE_PRODUCT: return evaluateProduct(n);
    case TABLE_JOIN: return evaluateJoin(rewriter, n);
    case TABLE_GROUP: return evaluateGroup(n);
    case TABLE_PROJECT: return evaluateTableProject(n);
    default: break;
  }
  Unhandled() << "Unexpected bag kind '" << n.getKind() << "' in node " << n
              << std::endl;
}

template <typename T1, typename T2, typename T3, typename T4, typename T5>
Node BagsUtils::evaluateBinaryOperation(const TNode& n,
                                        T1&& equal,
                                        T2&& less,
                                        T3&& greaterOrEqual,
                                        T4&& remainderOfA,
                                        T5&& remainderOfB)
{
  std::map<Node, Rational> elementsA = getBagElements(n[0]);
  std::map<Node, Rational> elementsB = getBagElements(n[1]);
  std::map<Node, Rational> elements;

  std::map<Node, Rational>::const_iterator itA = elementsA.begin();
  std::map<Node, Rational>::const_iterator itB = elementsB.begin();

  Trace("bags-evaluate") << "[NormalForm::evaluateBinaryOperation "
                         << n.getKind() << "] " << std::endl
                         << "elements A: " << elementsA << std::endl
                         << "elements B: " << elementsB << std::endl;

  while (itA != elementsA.end() && itB != elementsB.end())
  {
    if (itA->first == itB->first)
    {
      equal(elements, itA, itB);
      itA++;
      itB++;
    }
    else if (itA->first < itB->first)
    {
      less(elements, itA, itB);
      itA++;
    }
    else
    {
      greaterOrEqual(elements, itA, itB);
      itB++;
    }
  }

  // handle the remaining elements from A
  remainderOfA(elements, elementsA, itA);
  // handle the remaining elements from B
  remainderOfB(elements, elementsB, itB);

  Trace("bags-evaluate") << "elements: " << elements << std::endl;
  Node bag = constructConstantBagFromElements(n.getType(), elements);
  Trace("bags-evaluate") << "bag: " << bag << std::endl;
  return bag;
}

std::map<Node, Rational> BagsUtils::getBagElements(TNode n)
{
  std::map<Node, Rational> elements;
  if (n.getKind() == BAG_EMPTY)
  {
    return elements;
  }
  while (n.getKind() == kind::BAG_UNION_DISJOINT)
  {
    Assert(n[0].getKind() == kind::BAG_MAKE);
    Node element = n[0][0];
    Rational count = n[0][1].getConst<Rational>();
    elements[element] = count;
    n = n[1];
  }
  Assert(n.getKind() == kind::BAG_MAKE);
  Node lastElement = n[0];
  Rational lastCount = n[1].getConst<Rational>();
  elements[lastElement] = lastCount;
  return elements;
}

Node BagsUtils::constructConstantBagFromElements(
    TypeNode t, const std::map<Node, Rational>& elements)
{
  Assert(t.isBag());
  NodeManager* nm = NodeManager::currentNM();
  if (elements.empty())
  {
    return nm->mkConst(EmptyBag(t));
  }
  TypeNode elementType = t.getBagElementType();
  std::map<Node, Rational>::const_reverse_iterator it = elements.rbegin();
  Node bag = nm->mkNode(BAG_MAKE, it->first, nm->mkConstInt(it->second));
  while (++it != elements.rend())
  {
    Node n = nm->mkNode(BAG_MAKE, it->first, nm->mkConstInt(it->second));
    bag = nm->mkNode(BAG_UNION_DISJOINT, n, bag);
  }
  return bag;
}

Node BagsUtils::constructBagFromElements(TypeNode t,
                                         const std::map<Node, Node>& elements)
{
  Assert(t.isBag());
  NodeManager* nm = NodeManager::currentNM();
  if (elements.empty())
  {
    return nm->mkConst(EmptyBag(t));
  }
  TypeNode elementType = t.getBagElementType();
  std::map<Node, Node>::const_reverse_iterator it = elements.rbegin();
  Node bag = nm->mkNode(BAG_MAKE, it->first, it->second);
  while (++it != elements.rend())
  {
    Node n = nm->mkNode(BAG_MAKE, it->first, it->second);
    bag = nm->mkNode(BAG_UNION_DISJOINT, n, bag);
  }
  return bag;
}

Node BagsUtils::evaluateMakeBag(TNode n)
{
  // the case where n is const should be handled earlier.
  // here we handle the case where the multiplicity is zero or negative
  Assert(n.getKind() == BAG_MAKE && !n.isConst()
         && n[1].getConst<Rational>().sgn() < 1);
  Node emptybag = NodeManager::currentNM()->mkConst(EmptyBag(n.getType()));
  return emptybag;
}

Node BagsUtils::evaluateBagCount(TNode n)
{
  Assert(n.getKind() == BAG_COUNT);
  // Examples
  // --------
  // - (bag.count "x" (as bag.empty (Bag String))) = 0
  // - (bag.count "x" (bag "y" 5)) = 0
  // - (bag.count "x" (bag "x" 4)) = 4
  // - (bag.count "x" (bag.union_disjoint (bag "x" 4) (bag "y" 5)) = 4
  // - (bag.count "x" (bag.union_disjoint (bag "y" 5) (bag "z" 5)) = 0

  std::map<Node, Rational> elements = getBagElements(n[1]);
  std::map<Node, Rational>::iterator it = elements.find(n[0]);

  NodeManager* nm = NodeManager::currentNM();
  if (it != elements.end())
  {
    Node count = nm->mkConstInt(it->second);
    return count;
  }
  return nm->mkConstInt(Rational(0));
}

Node BagsUtils::evaluateDuplicateRemoval(TNode n)
{
  Assert(n.getKind() == BAG_DUPLICATE_REMOVAL);

  // Examples
  // --------
  //  - (bag.duplicate_removal (as bag.empty (Bag String))) = (as bag.empty (Bag
  //  String))
  //  - (bag.duplicate_removal (bag "x" 4)) = (bag "x" 1)
  //  - (bag.duplicate_removal (bag.disjoint_union (bag "x" 3) (bag "y" 5)) =
  //     (bag.disjoint_union (bag "x" 1) (bag "y" 1)

  std::map<Node, Rational> oldElements = getBagElements(n[0]);
  // copy elements from the old bag
  std::map<Node, Rational> newElements(oldElements);
  Rational one = Rational(1);
  std::map<Node, Rational>::iterator it;
  for (it = newElements.begin(); it != newElements.end(); it++)
  {
    it->second = one;
  }
  Node bag = constructConstantBagFromElements(n[0].getType(), newElements);
  return bag;
}

Node BagsUtils::evaluateUnionDisjoint(TNode n)
{
  Assert(n.getKind() == BAG_UNION_DISJOINT);
  // Example
  // -------
  // input: (bag.union_disjoint A B)
  //    where A = (bag.union_disjoint (bag "x" 4) (bag "z" 2)))
  //          B = (bag.union_disjoint (bag "x" 3) (bag "y" 1)))
  // output:
  //    (bag.union_disjoint A B)
  //        where A = (bag "x" 7)
  //              B = (bag.union_disjoint (bag "y" 1) (bag "z" 2)))

  auto equal = [](std::map<Node, Rational>& elements,
                  std::map<Node, Rational>::const_iterator& itA,
                  std::map<Node, Rational>::const_iterator& itB) {
    // compute the sum of the multiplicities
    elements[itA->first] = itA->second + itB->second;
  };

  auto less = [](std::map<Node, Rational>& elements,
                 std::map<Node, Rational>::const_iterator& itA,
                 std::map<Node, Rational>::const_iterator& itB) {
    // add the element to the result
    elements[itA->first] = itA->second;
  };

  auto greaterOrEqual = [](std::map<Node, Rational>& elements,
                           std::map<Node, Rational>::const_iterator& itA,
                           std::map<Node, Rational>::const_iterator& itB) {
    // add the element to the result
    elements[itB->first] = itB->second;
  };

  auto remainderOfA = [](std::map<Node, Rational>& elements,
                         std::map<Node, Rational>& elementsA,
                         std::map<Node, Rational>::const_iterator& itA) {
    // append the remainder of A
    while (itA != elementsA.end())
    {
      elements[itA->first] = itA->second;
      itA++;
    }
  };

  auto remainderOfB = [](std::map<Node, Rational>& elements,
                         std::map<Node, Rational>& elementsB,
                         std::map<Node, Rational>::const_iterator& itB) {
    // append the remainder of B
    while (itB != elementsB.end())
    {
      elements[itB->first] = itB->second;
      itB++;
    }
  };

  return evaluateBinaryOperation(
      n, equal, less, greaterOrEqual, remainderOfA, remainderOfB);
}

Node BagsUtils::evaluateUnionMax(TNode n)
{
  Assert(n.getKind() == BAG_UNION_MAX);
  // Example
  // -------
  // input: (bag.union_max A B)
  //    where A = (bag.union_disjoint (bag "x" 4) (bag "z" 2)))
  //          B = (bag.union_disjoint (bag "x" 3) (bag "y" 1)))
  // output:
  //    (bag.union_disjoint A B)
  //        where A = (bag "x" 4)
  //              B = (bag.union_disjoint (bag "y" 1) (bag "z" 2)))

  auto equal = [](std::map<Node, Rational>& elements,
                  std::map<Node, Rational>::const_iterator& itA,
                  std::map<Node, Rational>::const_iterator& itB) {
    // compute the maximum multiplicity
    elements[itA->first] = std::max(itA->second, itB->second);
  };

  auto less = [](std::map<Node, Rational>& elements,
                 std::map<Node, Rational>::const_iterator& itA,
                 std::map<Node, Rational>::const_iterator& itB) {
    // add to the result
    elements[itA->first] = itA->second;
  };

  auto greaterOrEqual = [](std::map<Node, Rational>& elements,
                           std::map<Node, Rational>::const_iterator& itA,
                           std::map<Node, Rational>::const_iterator& itB) {
    // add to the result
    elements[itB->first] = itB->second;
  };

  auto remainderOfA = [](std::map<Node, Rational>& elements,
                         std::map<Node, Rational>& elementsA,
                         std::map<Node, Rational>::const_iterator& itA) {
    // append the remainder of A
    while (itA != elementsA.end())
    {
      elements[itA->first] = itA->second;
      itA++;
    }
  };

  auto remainderOfB = [](std::map<Node, Rational>& elements,
                         std::map<Node, Rational>& elementsB,
                         std::map<Node, Rational>::const_iterator& itB) {
    // append the remainder of B
    while (itB != elementsB.end())
    {
      elements[itB->first] = itB->second;
      itB++;
    }
  };

  return evaluateBinaryOperation(
      n, equal, less, greaterOrEqual, remainderOfA, remainderOfB);
}

Node BagsUtils::evaluateIntersectionMin(TNode n)
{
  Assert(n.getKind() == BAG_INTER_MIN);
  // Example
  // -------
  // input: (bag.inter_min A B)
  //    where A = (bag.union_disjoint (bag "x" 4) (bag "z" 2)))
  //          B = (bag.union_disjoint (bag "x" 3) (bag "y" 1)))
  // output:
  //        (bag "x" 3)

  auto equal = [](std::map<Node, Rational>& elements,
                  std::map<Node, Rational>::const_iterator& itA,
                  std::map<Node, Rational>::const_iterator& itB) {
    // compute the minimum multiplicity
    elements[itA->first] = std::min(itA->second, itB->second);
  };

  auto less = [](std::map<Node, Rational>& elements,
                 std::map<Node, Rational>::const_iterator& itA,
                 std::map<Node, Rational>::const_iterator& itB) {
    // do nothing
  };

  auto greaterOrEqual = [](std::map<Node, Rational>& elements,
                           std::map<Node, Rational>::const_iterator& itA,
                           std::map<Node, Rational>::const_iterator& itB) {
    // do nothing
  };

  auto remainderOfA = [](std::map<Node, Rational>& elements,
                         std::map<Node, Rational>& elementsA,
                         std::map<Node, Rational>::const_iterator& itA) {
    // do nothing
  };

  auto remainderOfB = [](std::map<Node, Rational>& elements,
                         std::map<Node, Rational>& elementsB,
                         std::map<Node, Rational>::const_iterator& itB) {
    // do nothing
  };

  return evaluateBinaryOperation(
      n, equal, less, greaterOrEqual, remainderOfA, remainderOfB);
}

Node BagsUtils::evaluateDifferenceSubtract(TNode n)
{
  Assert(n.getKind() == BAG_DIFFERENCE_SUBTRACT);
  // Example
  // -------
  // input: (bag.difference_subtract A B)
  //    where A = (bag.union_disjoint (bag "x" 4) (bag "z" 2)))
  //          B = (bag.union_disjoint (bag "x" 3) (bag "y" 1)))
  // output:
  //    (bag.union_disjoint (bag "x" 1) (bag "z" 2))

  auto equal = [](std::map<Node, Rational>& elements,
                  std::map<Node, Rational>::const_iterator& itA,
                  std::map<Node, Rational>::const_iterator& itB) {
    // subtract the multiplicities
    elements[itA->first] = itA->second - itB->second;
  };

  auto less = [](std::map<Node, Rational>& elements,
                 std::map<Node, Rational>::const_iterator& itA,
                 std::map<Node, Rational>::const_iterator& itB) {
    // itA->first is not in B, so we add it to the difference subtract
    elements[itA->first] = itA->second;
  };

  auto greaterOrEqual = [](std::map<Node, Rational>& elements,
                           std::map<Node, Rational>::const_iterator& itA,
                           std::map<Node, Rational>::const_iterator& itB) {
    // itB->first is not in A, so we just skip it
  };

  auto remainderOfA = [](std::map<Node, Rational>& elements,
                         std::map<Node, Rational>& elementsA,
                         std::map<Node, Rational>::const_iterator& itA) {
    // append the remainder of A
    while (itA != elementsA.end())
    {
      elements[itA->first] = itA->second;
      itA++;
    }
  };

  auto remainderOfB = [](std::map<Node, Rational>& elements,
                         std::map<Node, Rational>& elementsB,
                         std::map<Node, Rational>::const_iterator& itB) {
    // do nothing
  };

  return evaluateBinaryOperation(
      n, equal, less, greaterOrEqual, remainderOfA, remainderOfB);
}

Node BagsUtils::evaluateDifferenceRemove(TNode n)
{
  Assert(n.getKind() == BAG_DIFFERENCE_REMOVE);
  // Example
  // -------
  // input: (bag.difference_remove A B)
  //    where A = (bag.union_disjoint (bag "x" 4) (bag "z" 2)))
  //          B = (bag.union_disjoint (bag "x" 3) (bag "y" 1)))
  // output:
  //    (bag "z" 2)

  auto equal = [](std::map<Node, Rational>& elements,
                  std::map<Node, Rational>::const_iterator& itA,
                  std::map<Node, Rational>::const_iterator& itB) {
    // skip the shared element by doing nothing
  };

  auto less = [](std::map<Node, Rational>& elements,
                 std::map<Node, Rational>::const_iterator& itA,
                 std::map<Node, Rational>::const_iterator& itB) {
    // itA->first is not in B, so we add it to the difference remove
    elements[itA->first] = itA->second;
  };

  auto greaterOrEqual = [](std::map<Node, Rational>& elements,
                           std::map<Node, Rational>::const_iterator& itA,
                           std::map<Node, Rational>::const_iterator& itB) {
    // itB->first is not in A, so we just skip it
  };

  auto remainderOfA = [](std::map<Node, Rational>& elements,
                         std::map<Node, Rational>& elementsA,
                         std::map<Node, Rational>::const_iterator& itA) {
    // append the remainder of A
    while (itA != elementsA.end())
    {
      elements[itA->first] = itA->second;
      itA++;
    }
  };

  auto remainderOfB = [](std::map<Node, Rational>& elements,
                         std::map<Node, Rational>& elementsB,
                         std::map<Node, Rational>::const_iterator& itB) {
    // do nothing
  };

  return evaluateBinaryOperation(
      n, equal, less, greaterOrEqual, remainderOfA, remainderOfB);
}

Node BagsUtils::evaluateChoose(TNode n)
{
  Assert(n.getKind() == BAG_CHOOSE);
  // Examples
  // --------
  // - (bag.choose (bag "x" 4)) = "x"

  if (n[0].getKind() == BAG_MAKE)
  {
    return n[0][0];
  }
  throw LogicException("BAG_CHOOSE_TOTAL is not supported yet");
}

Node BagsUtils::evaluateCard(TNode n)
{
  Assert(n.getKind() == BAG_CARD);
  // Examples
  // --------
  //  - (card (as bag.empty (Bag String))) = 0
  //  - (bag.choose (bag "x" 4)) = 4
  //  - (bag.choose (bag.union_disjoint (bag "x" 4) (bag "y" 1))) = 5

  std::map<Node, Rational> elements = getBagElements(n[0]);
  Rational sum(0);
  for (std::pair<Node, Rational> element : elements)
  {
    sum += element.second;
  }

  NodeManager* nm = NodeManager::currentNM();
  Node sumNode = nm->mkConstInt(sum);
  return sumNode;
}

Node BagsUtils::evaluateIsSingleton(TNode n)
{
  Assert(n.getKind() == BAG_IS_SINGLETON);
  // Examples
  // --------
  // - (bag.is_singleton (as bag.empty (Bag String))) = false
  // - (bag.is_singleton (bag "x" 1)) = true
  // - (bag.is_singleton (bag "x" 4)) = false
  // - (bag.is_singleton (bag.union_disjoint (bag "x" 1) (bag "y" 1)))
  // = false

  if (n[0].getKind() == BAG_MAKE && n[0][1].getConst<Rational>().isOne())
  {
    return NodeManager::currentNM()->mkConst(true);
  }
  return NodeManager::currentNM()->mkConst(false);
}

Node BagsUtils::evaluateFromSet(TNode n)
{
  Assert(n.getKind() == BAG_FROM_SET);

  // Examples
  // --------
  //  - (bag.from_set (as set.empty (Set String))) = (as bag.empty (Bag String))
  //  - (bag.from_set (set.singleton "x")) = (bag "x" 1)
  //  - (bag.from_set (set.union (set.singleton "x") (set.singleton "y"))) =
  //     (bag.disjoint_union (bag "x" 1) (bag "y" 1))

  NodeManager* nm = NodeManager::currentNM();
  std::set<Node> setElements =
      sets::NormalForm::getElementsFromNormalConstant(n[0]);
  Rational one = Rational(1);
  std::map<Node, Rational> bagElements;
  for (const Node& element : setElements)
  {
    bagElements[element] = one;
  }
  TypeNode bagType = nm->mkBagType(n[0].getType().getSetElementType());
  Node bag = constructConstantBagFromElements(bagType, bagElements);
  return bag;
}

Node BagsUtils::evaluateToSet(TNode n)
{
  Assert(n.getKind() == BAG_TO_SET);

  // Examples
  // --------
  //  - (bag.to_set (as bag.empty (Bag String))) = (as set.empty (Set String))
  //  - (bag.to_set (bag "x" 4)) = (set.singleton "x")
  //  - (bag.to_set (bag.disjoint_union (bag "x" 3) (bag "y" 5)) =
  //     (set.union (set.singleton "x") (set.singleton "y")))

  NodeManager* nm = NodeManager::currentNM();
  std::map<Node, Rational> bagElements = getBagElements(n[0]);
  std::set<Node> setElements;
  std::map<Node, Rational>::const_reverse_iterator it;
  for (it = bagElements.rbegin(); it != bagElements.rend(); it++)
  {
    setElements.insert(it->first);
  }
  TypeNode setType = nm->mkSetType(n[0].getType().getBagElementType());
  Node set = sets::NormalForm::elementsToSet(setElements, setType);
  return set;
}

Node BagsUtils::evaluateBagMap(TNode n)
{
  Assert(n.getKind() == BAG_MAP);

  // Examples
  // --------
  // - (bag.map ((lambda ((x String)) "z")
  //            (bag.union_disjoint (bag "a" 2) (bag "b" 3)) =
  //     (bag.union_disjoint
  //       (bag ((lambda ((x String)) "z") "a") 2)
  //       (bag ((lambda ((x String)) "z") "b") 3)) =
  //     (bag "z" 5)

  std::map<Node, Rational> elements = BagsUtils::getBagElements(n[1]);
  std::map<Node, Rational> mappedElements;
  std::map<Node, Rational>::iterator it = elements.begin();
  NodeManager* nm = NodeManager::currentNM();
  while (it != elements.end())
  {
    Node mappedElement = nm->mkNode(APPLY_UF, n[0], it->first);
    mappedElements[mappedElement] = it->second;
    ++it;
  }
  TypeNode t = nm->mkBagType(n[0].getType().getRangeType());
  Node ret = BagsUtils::constructConstantBagFromElements(t, mappedElements);
  return ret;
}

Node BagsUtils::evaluateBagFilter(TNode n)
{
  Assert(n.getKind() == BAG_FILTER);

  // - (bag.filter p (as bag.empty (Bag T)) = (as bag.empty (Bag T))
  // - (bag.filter p (bag.union_disjoint (bag "a" 3) (bag "b" 2))) =
  //   (bag.union_disjoint
  //     (ite (p "a") (bag "a" 3) (as bag.empty (Bag T)))
  //     (ite (p "b") (bag "b" 2) (as bag.empty (Bag T)))

  Node P = n[0];
  Node A = n[1];
  TypeNode bagType = A.getType();
  NodeManager* nm = NodeManager::currentNM();
  Node empty = nm->mkConst(EmptyBag(bagType));

  std::map<Node, Rational> elements = getBagElements(n[1]);
  std::vector<Node> bags;

  for (const auto& [e, count] : elements)
  {
    Node multiplicity = nm->mkConstInt(count);
    Node bag = nm->mkNode(BAG_MAKE, e, multiplicity);
    Node pOfe = nm->mkNode(APPLY_UF, P, e);
    Node ite = nm->mkNode(ITE, pOfe, bag, empty);
    bags.push_back(ite);
  }
  Node ret = computeDisjointUnion(bagType, bags);
  return ret;
}

Node BagsUtils::evaluateBagFold(TNode n)
{
  Assert(n.getKind() == BAG_FOLD);

  // Examples
  // --------
  // minimum string
  // - (bag.fold
  //     ((lambda ((x String) (y String)) (ite (str.< x y) x y))
  //     ""
  //     (bag.union_disjoint (bag "a" 2) (bag "b" 3))
  //   = "a"

  Node f = n[0];    // combining function
  Node ret = n[1];  // initial value
  Node A = n[2];    // bag
  std::map<Node, Rational> elements = BagsUtils::getBagElements(A);

  std::map<Node, Rational>::iterator it = elements.begin();
  NodeManager* nm = NodeManager::currentNM();
  while (it != elements.end())
  {
    // apply the combination function n times, where n is the multiplicity
    Rational count = it->second;
    Assert(count.sgn() >= 0) << "negative multiplicity" << std::endl;
    while (!count.isZero())
    {
      ret = nm->mkNode(APPLY_UF, f, it->first, ret);
      count = count - 1;
    }
    ++it;
  }
  return ret;
}

Node BagsUtils::evaluateBagPartition(Rewriter* rewriter, TNode n)
{
  Assert(n.getKind() == BAG_PARTITION);
  NodeManager* nm = NodeManager::currentNM();

  // Examples
  // --------
  // minimum string
  // - (bag.partition
  //     ((lambda ((x Int) (y Int)) (= 0 (+ x y)))
  //     (bag.union_disjoint
  //       (bag 1 20) (bag (- 1) 50)
  //       (bag 2 30) (bag (- 2) 60)
  //       (bag 3 40) (bag (- 3) 70)
  //       (bag 4 100)))
  //   = (bag.union_disjoint
  //       (bag (bag 4 100) 1)
  //       (bag (bag.union_disjoint (bag 1 20) (bag (- 1) 50)) 1)
  //       (bag (bag.union_disjoint (bag 2 30) (bag (- 2) 60)) 1)
  //       (bag (bag.union_disjoint (bag 3 40) (bag (- 3) 70)) 1)))

  Node r = n[0];  // equivalence relation
  Node A = n[1];  // bag
  TypeNode bagType = A.getType();
  TypeNode partitionType = n.getType();
  std::map<Node, Rational> elements = BagsUtils::getBagElements(A);
  Trace("bags-partition") << "elements: " << elements << std::endl;
  // a simple map from elements to equivalent classes with this invariant:
  // each key element must appear exactly once in one of the values.
  std::map<Node, std::set<Node>> sets;
  std::set<Node> emptyClass;
  for (const auto& pair : elements)
  {
    // initially each singleton element is an equivalence class
    sets[pair.first] = {pair.first};
  }
  for (std::map<Node, Rational>::iterator i = elements.begin();
       i != elements.end();
       ++i)
  {
    if (sets[i->first].empty())
    {
      // skip this element since its equivalent class has already been processed
      continue;
    }
    std::map<Node, Rational>::iterator j = i;
    ++j;
    while (j != elements.end())
    {
      Node sameClass = nm->mkNode(APPLY_UF, r, i->first, j->first);
      sameClass = rewriter->rewrite(sameClass);
      if (!sameClass.isConst())
      {
        // we can not pursue further, so we return n itself
        return n;
      }
      if (sameClass.getConst<bool>())
      {
        // add element j to the equivalent class
        sets[i->first].insert(j->first);
        // mark the equivalent class of j as processed
        sets[j->first] = emptyClass;
      }
      ++j;
    }
  }

  // construct the partition parts
  std::map<Node, Rational> parts;
  for (std::pair<Node, std::set<Node>> pair : sets)
  {
    const std::set<Node>& eqc = pair.second;
    if (eqc.empty())
    {
      continue;
    }
    std::vector<Node> bags;
    for (const Node& node : eqc)
    {
      Node bag = nm->mkNode(BAG_MAKE, node, nm->mkConstInt(elements[node]));
      bags.push_back(bag);
    }
    Node part = computeDisjointUnion(bagType, bags);
    // each part in the partitions has multiplicity one
    parts[part] = Rational(1);
  }
  Node ret = constructConstantBagFromElements(partitionType, parts);
  Trace("bags-partition") << "ret: " << ret << std::endl;
  return ret;
}

Node BagsUtils::evaluateTableAggregate(Rewriter* rewriter, TNode n)
{
  Assert(n.getKind() == TABLE_AGGREGATE);
  if (!(n[1].isConst() && n[2].isConst()))
  {
    // we can't proceed further.
    return n;
  }

  Node reduction = BagReduction::reduceAggregateOperator(n);
  return reduction;
}

Node BagsUtils::constructProductTuple(TNode n, TNode e1, TNode e2)
{
  Assert(n.getKind() == TABLE_PRODUCT || n.getKind() == TABLE_JOIN);
  Node A = n[0];
  Node B = n[1];
  TypeNode typeA = A.getType().getBagElementType();
  TypeNode typeB = B.getType().getBagElementType();
  Assert(e1.getType() == typeA);
  Assert(e2.getType() == typeB);

  TypeNode productTupleType = n.getType().getBagElementType();
  Node tuple = TupleUtils::concatTuples(productTupleType, e1, e2);
  return tuple;
}

Node BagsUtils::evaluateProduct(TNode n)
{
  Assert(n.getKind() == TABLE_PRODUCT);

  // Examples
  // --------
  //
  // - (table.product (bag (tuple "a") 4) (bag (tuple true) 5)) =
  //     (bag (tuple "a" true) 20

  Node A = n[0];
  Node B = n[1];

  std::map<Node, Rational> elementsA = BagsUtils::getBagElements(A);
  std::map<Node, Rational> elementsB = BagsUtils::getBagElements(B);

  std::map<Node, Rational> elements;

  for (const auto& [a, countA] : elementsA)
  {
    for (const auto& [b, countB] : elementsB)
    {
      Node element = constructProductTuple(n, a, b);
      elements[element] = countA * countB;
    }
  }

  Node ret = BagsUtils::constructConstantBagFromElements(n.getType(), elements);
  return ret;
}

Node BagsUtils::evaluateJoin(Rewriter* rewriter, TNode n)
{
  Assert(n.getKind() == TABLE_JOIN);

  Node A = n[0];
  Node B = n[1];
  auto [aIndices, bIndices] = splitTableJoinIndices(n);

  std::map<Node, Rational> elementsA = BagsUtils::getBagElements(A);
  std::map<Node, Rational> elementsB = BagsUtils::getBagElements(B);

  std::map<Node, Rational> elements;

  for (const auto& [a, countA] : elementsA)
  {
    Node aProjection = TupleUtils::getTupleProjection(aIndices, a);
    aProjection = rewriter->rewrite(aProjection);
    Assert(aProjection.isConst());
    for (const auto& [b, countB] : elementsB)
    {
      Node bProjection = TupleUtils::getTupleProjection(bIndices, b);
      bProjection = rewriter->rewrite(bProjection);
      Assert(bProjection.isConst());
      if (aProjection == bProjection)
      {
        Node element = constructProductTuple(n, a, b);
        elements[element] = countA * countB;
      }
    }
  }

  Node ret = BagsUtils::constructConstantBagFromElements(n.getType(), elements);
  return ret;
}

Node BagsUtils::evaluateGroup(TNode n)
{
  Assert(n.getKind() == TABLE_GROUP);

  NodeManager* nm = NodeManager::currentNM();

  Node A = n[0];
  TypeNode bagType = A.getType();
  TypeNode partitionType = n.getType();

  std::vector<uint32_t> indices =
      n.getOperator().getConst<ProjectOp>().getIndices();

  std::map<Node, Rational> elements = BagsUtils::getBagElements(A);
  Trace("bags-group") << "elements: " << elements << std::endl;
  // a simple map from elements to equivalent classes with this invariant:
  // each key element must appear exactly once in one of the values.
  std::map<Node, std::set<Node>> sets;
  std::set<Node> emptyClass;
  for (const auto& pair : elements)
  {
    // initially each singleton element is an equivalence class
    sets[pair.first] = {pair.first};
  }
  for (std::map<Node, Rational>::iterator i = elements.begin();
       i != elements.end();
       ++i)
  {
    if (sets[i->first].empty())
    {
      // skip this element since its equivalent class has already been processed
      continue;
    }
    std::map<Node, Rational>::iterator j = i;
    ++j;
    while (j != elements.end())
    {
      if (TupleUtils::sameProjection(indices, i->first, j->first))
      {
        // add element j to the equivalent class
        sets[i->first].insert(j->first);
        // mark the equivalent class of j as processed
        sets[j->first] = emptyClass;
      }
      ++j;
    }
  }

  // construct the partition parts
  std::map<Node, Rational> parts;
  for (std::pair<Node, std::set<Node>> pair : sets)
  {
    const std::set<Node>& eqc = pair.second;
    if (eqc.empty())
    {
      continue;
    }
    std::vector<Node> bags;
    for (const Node& node : eqc)
    {
      Node bag = nm->mkNode(BAG_MAKE, node, nm->mkConstInt(elements[node]));
      bags.push_back(bag);
    }
    Node part = computeDisjointUnion(bagType, bags);
    // each part in the partitions has multiplicity one
    parts[part] = Rational(1);
  }
  if (parts.empty())
  {
    // add an empty part
    Node emptyPart = nm->mkConst(EmptyBag(bagType));
    parts[emptyPart] = Rational(1);
  }
  Node ret = constructConstantBagFromElements(partitionType, parts);
  Trace("bags-group") << "ret: " << ret << std::endl;
  return ret;
}

Node BagsUtils::evaluateTableProject(TNode n)
{
  Assert(n.getKind() == TABLE_PROJECT);
  Node bagMap = BagReduction::reduceProjectOperator(n);
  Node ret = evaluateBagMap(bagMap);
  return ret;
}

std::pair<std::vector<uint32_t>, std::vector<uint32_t>>
BagsUtils::splitTableJoinIndices(Node n)
{
  Assert(n.getKind() == kind::TABLE_JOIN && n.hasOperator()
         && n.getOperator().getKind() == kind::TABLE_JOIN_OP);
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  const std::vector<uint32_t>& indices = op.getIndices();
  size_t joinSize = indices.size() / 2;
  std::vector<uint32_t> indices1(joinSize), indices2(joinSize);

  for (size_t i = 0, index = 0; i < joinSize; i += 2, ++index)
  {
    indices1[index] = indices[i];
    indices2[index] = indices[i + 1];
  }
  return std::make_pair(indices1, indices2);
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
