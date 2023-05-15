/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Set enumerator implementation.
 */

#include "theory/sets/theory_sets_type_enumerator.h"

#include "util/bitvector.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

SetEnumerator::SetEnumerator(TypeNode type, TypeEnumeratorProperties* tep)
    : TypeEnumeratorBase<SetEnumerator>(type),
      d_nodeManager(NodeManager::currentNM()),
      d_elementEnumerator(type.getSetElementType(), tep),
      d_isFinished(false),
      d_currentSetIndex(0),
      d_currentSet()
{
  d_currentSet = d_nodeManager->mkConst(EmptySet(type));
}

SetEnumerator::SetEnumerator(const SetEnumerator& enumerator)
    : TypeEnumeratorBase<SetEnumerator>(enumerator.getType()),
      d_nodeManager(enumerator.d_nodeManager),
      d_elementEnumerator(enumerator.d_elementEnumerator),
      d_isFinished(enumerator.d_isFinished),
      d_currentSetIndex(enumerator.d_currentSetIndex),
      d_currentSet(enumerator.d_currentSet)
{
}

SetEnumerator::~SetEnumerator() {}

Node SetEnumerator::operator*()
{
  if (d_isFinished)
  {
    throw NoMoreValuesException(getType());
  }

  Trace("set-type-enum") << "SetEnumerator::operator* d_currentSet = "
                         << d_currentSet << std::endl;

  return d_currentSet;
}

SetEnumerator& SetEnumerator::operator++()
{
  if (d_isFinished)
  {
    Trace("set-type-enum") << "SetEnumerator::operator++ finished!"
                           << std::endl;
    Trace("set-type-enum") << "SetEnumerator::operator++ d_currentSet = "
                           << d_currentSet << std::endl;
    return *this;
  }

  d_currentSetIndex++;

  // if the index is a power of 2, get a new element from d_elementEnumerator
  if (d_currentSetIndex == static_cast<unsigned>(1 << d_elementsSoFar.size()))
  {
    // if there are no more values from d_elementEnumerator, set d_isFinished
    // to true
    if (d_elementEnumerator.isFinished())
    {
      d_isFinished = true;

      Trace("set-type-enum")
          << "SetEnumerator::operator++ finished!" << std::endl;
      Trace("set-type-enum")
          << "SetEnumerator::operator++ d_currentSet = " << d_currentSet
          << std::endl;
      return *this;
    }

    // get a new element and return it as a singleton set
    Node element = *d_elementEnumerator;
    d_elementsSoFar.push_back(element);
    d_currentSet = d_nodeManager->mkNode(kind::SET_SINGLETON, element);
    d_elementEnumerator++;
  }
  else
  {
    // determine which elements are included in the set
    BitVector indices = BitVector(d_elementsSoFar.size(), d_currentSetIndex);
    std::vector<Node> elements;
    for (unsigned i = 0; i < d_elementsSoFar.size(); i++)
    {
      // add the element to the set if its corresponding bit is set
      if (indices.isBitSet(i))
      {
        elements.push_back(d_elementsSoFar[i]);
      }
    }
    d_currentSet = NormalForm::elementsToSet(
        std::set<TNode>(elements.begin(), elements.end()), getType());
  }

  Assert(d_currentSet.isConst());

  Trace("set-type-enum") << "SetEnumerator::operator++ d_elementsSoFar = "
                         << d_elementsSoFar << std::endl;
  Trace("set-type-enum") << "SetEnumerator::operator++ d_currentSet = "
                         << d_currentSet << std::endl;

  return *this;
}

bool SetEnumerator::isFinished()
{
  Trace("set-type-enum") << "SetEnumerator::isFinished = " << d_isFinished
                         << std::endl;
  return d_isFinished;
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
