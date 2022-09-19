/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Enumerators for rationals and integers.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__TYPE_ENUMERATOR_H
#define CVC5__THEORY__FF__TYPE_ENUMERATOR_H

#include "expr/kind.h"
#include "expr/type_node.h"
#include "theory/type_enumerator.h"
#include "util/ff_val.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

class FiniteFieldEnumerator : public TypeEnumeratorBase<FiniteFieldEnumerator>
{
  Integer d_modulus;
  Integer d_currentInt;

 public:
  FiniteFieldEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr)
      : TypeEnumeratorBase<FiniteFieldEnumerator>(type),
        d_modulus(type.getFfSize()),
        d_currentInt(0)
  {
    // our enumerator assumes this is a prime field
    Assert(d_modulus.isProbablePrime());
  }

  Node operator*() override
  {
    if (d_currentInt == d_modulus)
    {
      throw NoMoreValuesException(getType());
    }
    return NodeManager::currentNM()->mkConst<FfVal>(
        FfVal(d_currentInt, d_modulus));
  }

  FiniteFieldEnumerator& operator++() override
  {
    d_currentInt += 1;
    return *this;
  }

  bool isFinished() override { return d_currentInt == d_modulus; }
}; /* FiniteFieldEnumerator */

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__TYPE_ENUMERATOR_H */
