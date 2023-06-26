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
 * Bag enumerator implementation
 */

#include "theory/bags/theory_bags_type_enumerator.h"

#include "expr/emptybag.h"
#include "theory/bags/bags_utils.h"
#include "theory_bags_type_enumerator.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

BagEnumerator::BagEnumerator(TypeNode type, TypeEnumeratorProperties* tep)
    : TypeEnumeratorBase<BagEnumerator>(type),
      d_nodeManager(NodeManager::currentNM()),
      d_elementTypeEnumerator(type.getBagElementType(), tep)
{
  d_currentBag = d_nodeManager->mkConst(EmptyBag(type));
  d_element = *d_elementTypeEnumerator;
}

BagEnumerator::BagEnumerator(const BagEnumerator& enumerator)
    : TypeEnumeratorBase<BagEnumerator>(enumerator.getType()),
      d_nodeManager(enumerator.d_nodeManager),
      d_elementTypeEnumerator(enumerator.d_elementTypeEnumerator),
      d_currentBag(enumerator.d_currentBag),
      d_element(enumerator.d_element)
{
}

BagEnumerator::~BagEnumerator() {}

Node BagEnumerator::operator*()
{
  Trace("bag-type-enum") << "BagEnumerator::operator* d_currentBag = "
                         << d_currentBag << std::endl;

  return d_currentBag;
}

BagEnumerator& BagEnumerator::operator++()
{
  if (d_currentBag.getKind() == kind::BAG_EMPTY)
  {
    // return (bag d_element 1)
    Node one = d_nodeManager->mkConstInt(Rational(1));
    TypeNode elementType = d_elementTypeEnumerator.getType();
    Node singleton = d_nodeManager->mkNode(BAG_MAKE, d_element, one);
    d_currentBag = singleton;
  }
  else
  {
    // increase the multiplicity of one of the elements in the current bag
    std::map<Node, Rational> elements = BagsUtils::getBagElements(d_currentBag);
    Node element = elements.begin()->first;
    elements[element] = elements[element] + Rational(1);
    d_currentBag = BagsUtils::constructConstantBagFromElements(
        d_currentBag.getType(), elements);
  }

  Assert(d_currentBag.isConst());

  Trace("bag-type-enum") << "BagEnumerator::operator++ d_currentBag = "
                         << d_currentBag << std::endl;
  return *this;
}

bool BagEnumerator::isFinished()
{
  // bags sequence is infinite and it never ends
  return false;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
