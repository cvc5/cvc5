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
  /** type properties */
  NodeManager* d_nm;
  TypeEnumerator d_elementTypeEnumerator;
  bool d_finished;

 public:
  SetEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr)
      : TypeEnumeratorBase<SetEnumerator>(type),
        d_nm(NodeManager::currentNM()),
        d_elementTypeEnumerator(type.getSetElementType(), tep),
        d_finished(false)
  {
  }

  SetEnumerator(const SetEnumerator& enumerator)
      : TypeEnumeratorBase<SetEnumerator>(enumerator.getType()),
        d_nm(enumerator.d_nm),
        d_elementTypeEnumerator(enumerator.d_elementTypeEnumerator),
        d_finished(enumerator.d_finished)
  {
  }

  ~SetEnumerator() {}

  Node operator*() override
  {
    if (d_finished)
    {
      throw NoMoreValuesException(getType());
    }

    Trace("set-type-enum") << "elements: " << *d_elementTypeEnumerator
                           << std::endl;

    Node n = d_nm->mkNode(Kind::SINGLETON, *d_elementTypeEnumerator);

    Assert(n.isConst());
    Assert(n == Rewriter::rewrite(n));

    return n;
  }

  SetEnumerator& operator++() override
  {
    Trace("set-type-enum") << "operator++ called, **this = " << **this
                           << std::endl;

    Trace("set-type-enum") << "d_constituentVec: "
                           << (*d_elementTypeEnumerator).getType() << std::endl;

    if (d_finished)
    {
      Trace("set-type-enum") << "operator++ finished!" << std::endl;
      return *this;
    }

    Node last_pre_increment = *d_elementTypeEnumerator;

    ++d_elementTypeEnumerator;

    TypeEnumerator* newEnumerator = new TypeEnumerator(d_elementTypeEnumerator);
    ++(*newEnumerator);
    if (newEnumerator->isFinished())
    {
      Trace("set-type-enum") << "operator++ finished!" << std::endl;
      delete newEnumerator;
      d_finished = true;
      return *this;
    }

    Trace("set-type-enum") << "operator++ returning, **this = " << **this
                           << std::endl;
    return *this;
  }

  bool isFinished() override
  {
    Trace("set-type-enum") << "isFinished returning: " << d_finished
                           << std::endl;
    return d_finished;
  }

}; /* class SetEnumerator */

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SETS__TYPE_ENUMERATOR_H */
