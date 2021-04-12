/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Enumerator for uninterpreted sorts and functions.
 */

#include "theory/builtin/type_enumerator.h"

#include "theory/builtin/theory_builtin_rewriter.h"

namespace cvc5 {
namespace theory {
namespace builtin {

FunctionEnumerator::FunctionEnumerator(TypeNode type,
                                       TypeEnumeratorProperties* tep)
    : TypeEnumeratorBase<FunctionEnumerator>(type),
      d_arrayEnum(TheoryBuiltinRewriter::getArrayTypeForFunctionType(type), tep)
{
  Assert(type.getKind() == kind::FUNCTION_TYPE);
  d_bvl = NodeManager::currentNM()->getBoundVarListForFunctionType(type);
}

Node FunctionEnumerator::operator*()
{
  if (isFinished())
  {
    throw NoMoreValuesException(getType());
  }
  Node a = *d_arrayEnum;
  return TheoryBuiltinRewriter::getLambdaForArrayRepresentation(a, d_bvl);
}

FunctionEnumerator& FunctionEnumerator::operator++()
{
  ++d_arrayEnum;
  return *this;
}

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5
