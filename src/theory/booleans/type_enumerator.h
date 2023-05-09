/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Tim King, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An enumerator for Booleans.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BOOLEANS__TYPE_ENUMERATOR_H
#define CVC5__THEORY__BOOLEANS__TYPE_ENUMERATOR_H

#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/kind.h"

namespace cvc5::internal {
namespace theory {
namespace booleans {

class BooleanEnumerator : public TypeEnumeratorBase<BooleanEnumerator> {
  enum { FALSE, TRUE, DONE } d_value;

 public:
  BooleanEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr)
      : TypeEnumeratorBase<BooleanEnumerator>(type), d_value(FALSE)
  {
    Assert(type.getKind() == kind::TYPE_CONSTANT
           && type.getConst<TypeConstant>() == BOOLEAN_TYPE);
  }

  Node operator*() override {
    switch(d_value) {
    case FALSE:
      return NodeManager::currentNM()->mkConst(false);
    case TRUE:
      return NodeManager::currentNM()->mkConst(true);
    default:
      throw NoMoreValuesException(getType());
    }
  }

  BooleanEnumerator& operator++() override
  {
    // sequence is FALSE, TRUE
    if(d_value == FALSE) {
      d_value = TRUE;
    } else {
      d_value = DONE;
    }
    return *this;
  }

  bool isFinished() override { return d_value == DONE; }
};/* class BooleanEnumerator */

}  // namespace booleans
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BOOLEANS__TYPE_ENUMERATOR_H */
