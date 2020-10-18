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

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

bool NormalForm::checkNormalConstant(TNode n)
{
  if (n.getKind() == EMPTYBAG)
  {
    // empty bags are already normalized
    return true;
  }
  if (n.getKind() == MK_BAG)
  {
    // see MkBagTypeRule::computeIsConst
    return n.isConst();
  }
  if (n.getKind() == UNION_DISJOINT)
  {
    if (!(n[0].getKind() == kind::MK_BAG && n[0].isConst()))
    {
      return false;
    }

    Node previousElement = n[0][0];
    Node current = n[1];
    while (current.getKind() == UNION_DISJOINT)
    {
      if (!(current[0].getKind() == kind::MK_BAG && current[0].isConst()))
      {
        return false;
      }
      if (previousElement >= current[0][0])
      {
        return false;
      }
      previousElement = current[0][0];
      current = current[1];
    }
    // check last element
    if (!(current.getKind() == kind::MK_BAG && current.isConst()))
    {
      return false;
    }
    if (previousElement >= current[0])
    {
      return false;
    }
    return true;
  }

  // only emptybag, MK_BAG, and UNION_DISJOINT
  // can be in normal form
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
    case UNION_DISJOINT: return evaluateUnionDisjoint(n); break;
    default:
    {
    }
    break;
  }
  Unhandled() << "Unexpected kind '" << n.getKind() << "' in node " << n
              << std::endl;
}

Node NormalForm::evaluateMakeBag(TNode n)
{
  Assert(n.getKind() == MK_BAG && !n.isConst()
         && n[1].getConst<Rational>().sgn() < 1);
  Node emptybag = NodeManager::currentNM()->mkConst(EmptyBag(n.getType()));
  return emptybag;
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

  std::map<Node, Rational> elementsA = getBagElements(n[0]);
  std::map<Node, Rational> elementsB = getBagElements(n[1]);
  std::map<Node, Rational> elements;

  std::map<Node, Rational>::const_iterator itA = elementsA.begin();
  std::map<Node, Rational>::const_iterator itB = elementsB.begin();

  Trace("bags-evaluate") << "NormalForm::evaluateUnionDisjoint elements A: "
                         << elementsA << std::endl;
  Trace("bags-evaluate") << "NormalForm::evaluateUnionDisjoint elements B: "
                         << elementsA << std::endl;

  while (itA != elementsA.end() && itB != elementsB.end())
  {
    if (itA->first == itB->first)
    {
      elements[itA->first] = itA->second + itB->second;
      itA++;
      itB++;
    }
    else if (itA->first < itB->first)
    {
      elements[itA->first] = itA->second;
      itA++;
    }
    else
    {
      elements[itB->first] = itB->second;
      itB++;
    }
  }

  // insert the remaining elements from A
  while (itA != elementsA.end())
  {
    elements[itA->first] = itA->second;
    itA++;
  }

  // insert the remaining elements from B
  while (itB != elementsB.end())
  {
    elements[itB->first] = itB->second;
    itB++;
  }

  Trace("bags-evaluate") << "NormalForm::evaluateUnionDisjoint elements: "
                         << elements << std::endl;
  Node value = constructBagFromElements(n.getType(), elements);
  return value;
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

Node NormalForm::constructBagFromElements(TypeNode t,
                                          const std::map<Node, Rational>& map)
{
  Assert(t.isBag());
  NodeManager* nm = NodeManager::currentNM();
  if (map.empty())
  {
    return nm->mkConst(EmptyBag(t));
  }
  TypeNode elementType = t.getBagElementType();
  std::map<Node, Rational>::const_reverse_iterator it = map.rbegin();
  Node bag =
      nm->mkBag(elementType, it->first, nm->mkConst<Rational>(it->second));
  while (++it != map.rend())
  {
    Node n =
        nm->mkBag(elementType, it->first, nm->mkConst<Rational>(it->second));
    bag = nm->mkNode(UNION_DISJOINT, n, bag);
  }
  return bag;
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4