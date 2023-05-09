/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Enumerator for functions.
 */

#include "theory/uf/type_enumerator.h"

#include "expr/function_array_const.h"
#include "theory/uf/function_const.h"

namespace cvc5::internal {
namespace theory {
namespace uf {

FunctionEnumerator::FunctionEnumerator(TypeNode type,
                                       TypeEnumeratorProperties* tep)
    : TypeEnumeratorBase<FunctionEnumerator>(type),
      d_arrayEnum(FunctionConst::getArrayTypeForFunctionType(type), tep)
{
  Assert(type.getKind() == kind::FUNCTION_TYPE);
}

Node FunctionEnumerator::operator*()
{
  if (isFinished())
  {
    throw NoMoreValuesException(getType());
  }
  Node a = *d_arrayEnum;
  return NodeManager::currentNM()->mkConst(FunctionArrayConst(getType(), a));
}

FunctionEnumerator& FunctionEnumerator::operator++()
{
  ++d_arrayEnum;
  return *this;
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
