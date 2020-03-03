/*********************                                                        */
/*! \file theory_sets_type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__TYPE_ENUMERATOR_H
#define CVC4__THEORY__SETS__TYPE_ENUMERATOR_H

#include "expr/kind.h"
#include "expr/type_node.h"
#include "theory/rewriter.h"
#include "theory/sets/normal_form.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace sets {

class SetEnumerator : public TypeEnumeratorBase<SetEnumerator>
{
 public:
  SetEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr)
      : TypeEnumeratorBase<SetEnumerator>(type),
        d_nodeManager(NodeManager::currentNM()),
        d_elementEnumerator(type.getSetElementType(), tep),
        d_isFinished(false),
        d_currentSetIndex(0),
        d_currentSet()
  {
    d_currentSet = d_nodeManager->mkConst(EmptySet(type.toType()));
  }

  SetEnumerator(const SetEnumerator& enumerator)
      : TypeEnumeratorBase<SetEnumerator>(enumerator.getType()),
        d_nodeManager(enumerator.d_nodeManager),
        d_elementEnumerator(enumerator.d_elementEnumerator),
        d_isFinished(enumerator.d_isFinished),
        d_currentSetIndex(enumerator.d_currentSetIndex),
        d_currentSet(enumerator.d_currentSet)
  {
  }

  ~SetEnumerator() {}

  Node operator*() override
  {
    if (d_isFinished)
    {
      throw NoMoreValuesException(getType());
    }

    return d_currentSet;
  }

  SetEnumerator& operator++() override
  {
    if (d_isFinished)
    {
      Trace("set-type-enum") << "operator++ finished!" << std::endl;
      return *this;
    }

    d_currentSetIndex++;

    // generate new element
    if (d_currentSetIndex == (unsigned)(1 << d_elementsSoFar.size()))
    {
      if (d_elementEnumerator.isFinished())
      {
        d_isFinished = true;
        return *this;
      }

      Node element = *d_elementEnumerator;
      d_elementsSoFar.push_back(element);
      d_currentSet = d_nodeManager->mkNode(Kind::SINGLETON, element);
      d_elementEnumerator++;
    }
    else
    {
      BitVector indices = BitVector(d_elementsSoFar.size(), d_currentSetIndex);
      std::vector<Node> elements;
      for (unsigned i = 0; i < d_elementsSoFar.size(); i++)
      {
        if (indices.isBitSet(i))
        {
          elements.push_back(d_elementsSoFar[i]);
        }
      }
      d_currentSet = NormalForm::elementsToSet(
          std::set<TNode>(elements.begin(), elements.end()), getType());
    }

    Assert(d_currentSet.isConst());
    Assert(d_currentSet == Rewriter::rewrite(d_currentSet));
    return *this;
  }

  bool isFinished() override
  {
    Trace("set-type-enum") << "isFinished returning: " << d_isFinished
                           << std::endl;
    return d_isFinished;
  }

 private:
  NodeManager* d_nodeManager;
  TypeEnumerator d_elementEnumerator;
  bool d_isFinished;
  std::vector<Node> d_elementsSoFar;
  unsigned int d_currentSetIndex;
  Node d_currentSet;
}; /* class SetEnumerator */

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SETS__TYPE_ENUMERATOR_H */
