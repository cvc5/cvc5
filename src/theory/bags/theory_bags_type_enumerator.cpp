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
 * Bag enumerator implementation
 */

#include "theory/bags/theory_bags_type_enumerator.h"

#include "expr/emptybag.h"
#include "theory/rewriter.h"
#include "theory_bags_type_enumerator.h"
#include "util/rational.h"

namespace cvc5 {
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
  // increase the multiplicity by one
  Node one = d_nodeManager->mkConst(Rational(1));
  TypeNode elementType = d_elementTypeEnumerator.getType();
  Node singleton = d_nodeManager->mkBag(elementType, d_element, one);
  if (d_currentBag.getKind() == kind::EMPTYBAG)
  {
    d_currentBag = singleton;
  }
  else
  {
    d_currentBag =
        d_nodeManager->mkNode(kind::UNION_DISJOINT, singleton, d_currentBag);
  }

  d_currentBag = Rewriter::rewrite(d_currentBag);

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
}  // namespace cvc5
