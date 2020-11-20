/*************************                                                    */
/*! \file normal_form.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **/

#include "normal_form.h"

#include "theory/sets/normal_form.h"
#include "theory/type_enumerator.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

bool NormalForm::isConstant(TNode n)
{
  if (n.getKind() == EMPTYBAG)
  {
    // empty bags are already normalized
    return true;
  }
  if (n.getKind() == MK_BAG)
  {
    // see the implementation in MkBagTypeRule::computeIsConst
    return n.isConst();
  }
  if (n.getKind() == UNION_DISJOINT)
  {
    if (!(n[0].getKind() == kind::MK_BAG && n[0].isConst()))
    {
      // the first child is not a constant
      return false;
    }
    // store the previous element to check the ordering of elements
    Node previousElement = n[0][0];
    Node current = n[1];
    while (current.getKind() == UNION_DISJOINT)
    {
      if (!(current[0].getKind() == kind::MK_BAG && current[0].isConst()))
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
    if (!(current.getKind() == kind::MK_BAG && current.isConst()))
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

  // only nodes with kinds EMPTY_BAG, MK_BAG, and UNION_DISJOINT can be
  // constants
  return false;
}

bool NormalForm::areChildrenConstants(TNode n)
{
  return std::all_of(n.begin(), n.end(), [](Node c) { return c.isConst(); });
}

Node NormalForm::evaluate(TNode n)
{
  Assert(areChildrenConstants(n));
  if (n.isConst())
  {
    // a constant node is already in a normal form
    return n;
  }
  switch (n.getKind())
  {
    case MK_BAG: return evaluateMakeBag(n);
    case BAG_COUNT: return evaluateBagCount(n);
    case DUPLICATE_REMOVAL: return evaluateDuplicateRemoval(n);
    case UNION_DISJOINT: return evaluateUnionDisjoint(n);
    case UNION_MAX: return evaluateUnionMax(n);
    case INTERSECTION_MIN: return evaluateIntersectionMin(n);
    case DIFFERENCE_SUBTRACT: return evaluateDifferenceSubtract(n);
    case DIFFERENCE_REMOVE: return evaluateDifferenceRemove(n);
    case BAG_CHOOSE: return evaluateChoose(n);
    case BAG_CARD: return evaluateCard(n);
    case BAG_IS_SINGLETON: return evaluateIsSingleton(n);
    case BAG_FROM_SET: return evaluateFromSet(n);
    case BAG_TO_SET: return evaluateToSet(n);
    default: break;
  }
  Unhandled() << "Unexpected bag kind '" << n.getKind() << "' in node " << n
              << std::endl;
}

template <typename T1, typename T2, typename T3, typename T4, typename T5>
Node NormalForm::evaluateBinaryOperation(const TNode& n,
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
  remainderOfA(elements, elementsB, itB);

  Trace("bags-evaluate") << "elements: " << elements << std::endl;
  Node bag = constructBagFromElements(n.getType(), elements);
  Trace("bags-evaluate") << "bag: " << bag << std::endl;
  return bag;
}

std::map<Node, Rational> NormalForm::getBagElements(TNode n)
{
  Assert(n.isConst()) << "node " << n << " is not in a normal form"
                      << std::endl;
  std::map<Node, Rational> elements;
  if (n.getKind() == EMPTYBAG)
  {
    return elements;
  }
  while (n.getKind() == kind::UNION_DISJOINT)
  {
    Assert(n[0].getKind() == kind::MK_BAG);
    Node element = n[0][0];
    Rational count = n[0][1].getConst<Rational>();
    elements[element] = count;
    n = n[1];
  }
  Assert(n.getKind() == kind::MK_BAG);
  Node lastElement = n[0];
  Rational lastCount = n[1].getConst<Rational>();
  elements[lastElement] = lastCount;
  return elements;
}

Node NormalForm::constructBagFromElements(
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
  Node bag =
      nm->mkBag(elementType, it->first, nm->mkConst<Rational>(it->second));
  while (++it != elements.rend())
  {
    Node n =
        nm->mkBag(elementType, it->first, nm->mkConst<Rational>(it->second));
    bag = nm->mkNode(UNION_DISJOINT, n, bag);
  }
  return bag;
}

Node NormalForm::evaluateMakeBag(TNode n)
{
  // the case where n is const should be handled earlier.
  // here we handle the case where the multiplicity is zero or negative
  Assert(n.getKind() == MK_BAG && !n.isConst()
         && n[1].getConst<Rational>().sgn() < 1);
  Node emptybag = NodeManager::currentNM()->mkConst(EmptyBag(n.getType()));
  return emptybag;
}

Node NormalForm::evaluateBagCount(TNode n)
{
  Assert(n.getKind() == BAG_COUNT);
  // Examples
  // --------
  // - (bag.count "x" (emptybag String)) = 0
  // - (bag.count "x" (mkBag "y" 5)) = 0
  // - (bag.count "x" (mkBag "x" 4)) = 4
  // - (bag.count "x" (union_disjoint (mkBag "x" 4) (mkBag "y" 5)) = 4
  // - (bag.count "x" (union_disjoint (mkBag "y" 5) (mkBag "z" 5)) = 0

  std::map<Node, Rational> elements = getBagElements(n[1]);
  std::map<Node, Rational>::iterator it = elements.find(n[0]);

  NodeManager* nm = NodeManager::currentNM();
  if (it != elements.end())
  {
    Node count = nm->mkConst(it->second);
    return count;
  }
  return nm->mkConst(Rational(0));
}

Node NormalForm::evaluateDuplicateRemoval(TNode n)
{
  Assert(n.getKind() == DUPLICATE_REMOVAL);

  // Examples
  // --------
  //  - (duplicate_removal (emptybag String)) = (emptybag String)
  //  - (duplicate_removal (mkBag "x" 4)) = (emptybag "x" 1)
  //  - (duplicate_removal (disjoint_union (mkBag "x" 3) (mkBag "y" 5)) =
  //     (disjoint_union (mkBag "x" 1) (mkBag "y" 1)

  std::map<Node, Rational> oldElements = getBagElements(n[0]);
  // copy elements from the old bag
  std::map<Node, Rational> newElements(oldElements);
  Rational one = Rational(1);
  std::map<Node, Rational>::iterator it;
  for (it = newElements.begin(); it != newElements.end(); it++)
  {
    it->second = one;
  }
  Node bag = constructBagFromElements(n[0].getType(), newElements);
  return bag;
}

Node NormalForm::evaluateUnionDisjoint(TNode n)
{
  Assert(n.getKind() == UNION_DISJOINT);
  // Example
  // -------
  // input: (union_disjoint A B)
  //    where A = (union_disjoint (MK_BAG "x" 4) (MK_BAG "z" 2)))
  //          B = (union_disjoint (MK_BAG "x" 3) (MK_BAG "y" 1)))
  // output:
  //    (union_disjoint A B)
  //        where A = (MK_BAG "x" 7)
  //              B = (union_disjoint (MK_BAG "y" 1) (MK_BAG "z" 2)))

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

Node NormalForm::evaluateUnionMax(TNode n)
{
  Assert(n.getKind() == UNION_MAX);
  // Example
  // -------
  // input: (union_max A B)
  //    where A = (union_disjoint (MK_BAG "x" 4) (MK_BAG "z" 2)))
  //          B = (union_disjoint (MK_BAG "x" 3) (MK_BAG "y" 1)))
  // output:
  //    (union_disjoint A B)
  //        where A = (MK_BAG "x" 4)
  //              B = (union_disjoint (MK_BAG "y" 1) (MK_BAG "z" 2)))

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

Node NormalForm::evaluateIntersectionMin(TNode n)
{
  Assert(n.getKind() == INTERSECTION_MIN);
  // Example
  // -------
  // input: (intersectionMin A B)
  //    where A = (union_disjoint (MK_BAG "x" 4) (MK_BAG "z" 2)))
  //          B = (union_disjoint (MK_BAG "x" 3) (MK_BAG "y" 1)))
  // output:
  //        (MK_BAG "x" 3)

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

Node NormalForm::evaluateDifferenceSubtract(TNode n)
{
  Assert(n.getKind() == DIFFERENCE_SUBTRACT);
  // Example
  // -------
  // input: (difference_subtract A B)
  //    where A = (union_disjoint (MK_BAG "x" 4) (MK_BAG "z" 2)))
  //          B = (union_disjoint (MK_BAG "x" 3) (MK_BAG "y" 1)))
  // output:
  //    (union_disjoint (MK_BAG "x" 1) (MK_BAG "z" 2))

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

Node NormalForm::evaluateDifferenceRemove(TNode n)
{
  Assert(n.getKind() == DIFFERENCE_REMOVE);
  // Example
  // -------
  // input: (difference_subtract A B)
  //    where A = (union_disjoint (MK_BAG "x" 4) (MK_BAG "z" 2)))
  //          B = (union_disjoint (MK_BAG "x" 3) (MK_BAG "y" 1)))
  // output:
  //    (MK_BAG "z" 2)

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

Node NormalForm::evaluateChoose(TNode n)
{
  Assert(n.getKind() == BAG_CHOOSE);
  // Examples
  // --------
  // - (choose (emptyBag String)) = "" // the empty string which is the first
  //   element returned by the type enumerator
  // - (choose (MK_BAG "x" 4)) = "x"
  // - (choose (union_disjoint (MK_BAG "x" 4) (MK_BAG "y" 1))) = "x"
  //     deterministically return the first element

  if (n[0].getKind() == EMPTYBAG)
  {
    TypeNode elementType = n[0].getType().getBagElementType();
    TypeEnumerator typeEnumerator(elementType);
    // get the first value from the typeEnumerator
    Node element = *typeEnumerator;
    return element;
  }

  if (n[0].getKind() == MK_BAG)
  {
    return n[0][0];
  }
  Assert(n[0].getKind() == UNION_DISJOINT);
  // return the first element
  // e.g. (choose (union_disjoint (MK_BAG "x" 4) (MK_BAG "y" 1)))
  return n[0][0][0];
}

Node NormalForm::evaluateCard(TNode n)
{
  Assert(n.getKind() == BAG_CARD);
  // Examples
  // --------
  //  - (card (emptyBag String)) = 0
  //  - (choose (MK_BAG "x" 4)) = 4
  //  - (choose (union_disjoint (MK_BAG "x" 4) (MK_BAG "y" 1))) = 5

  std::map<Node, Rational> elements = getBagElements(n[0]);
  Rational sum(0);
  for (std::pair<Node, Rational> element : elements)
  {
    sum += element.second;
  }

  NodeManager* nm = NodeManager::currentNM();
  Node sumNode = nm->mkConst(sum);
  return sumNode;
}

Node NormalForm::evaluateIsSingleton(TNode n)
{
  Assert(n.getKind() == BAG_IS_SINGLETON);
  // Examples
  // --------
  // - (bag.is_singleton (emptyBag String)) = false
  // - (bag.is_singleton (MK_BAG "x" 1)) = true
  // - (bag.is_singleton (MK_BAG "x" 4)) = false
  // - (bag.is_singleton (union_disjoint (MK_BAG "x" 1) (MK_BAG "y" 1))) = false

  if (n[0].getKind() == MK_BAG && n[0][1].getConst<Rational>().isOne())
  {
    return NodeManager::currentNM()->mkConst(true);
  }
  return NodeManager::currentNM()->mkConst(false);
}

Node NormalForm::evaluateFromSet(TNode n)
{
  Assert(n.getKind() == BAG_FROM_SET);

  // Examples
  // --------
  //  - (bag.from_set (emptyset String)) = (emptybag String)
  //  - (bag.from_set (singleton "x")) = (mkBag "x" 1)
  //  - (bag.from_set (union (singleton "x") (singleton "y"))) =
  //     (disjoint_union (mkBag "x" 1) (mkBag "y" 1))

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
  Node bag = constructBagFromElements(bagType, bagElements);
  return bag;
}

Node NormalForm::evaluateToSet(TNode n)
{
  Assert(n.getKind() == BAG_TO_SET);

  // Examples
  // --------
  //  - (bag.to_set (emptybag String)) = (emptyset String)
  //  - (bag.to_set (mkBag "x" 4)) = (singleton "x")
  //  - (bag.to_set (disjoint_union (mkBag "x" 3) (mkBag "y" 5)) =
  //     (union (singleton "x") (singleton "y")))

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

}  // namespace bags
}  // namespace theory
}  // namespace CVC4