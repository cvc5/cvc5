/*********************                                                        */
/*! \file type_enumerator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumerator for uninterpreted sorts and functions.
 **
 ** Enumerator for uninterpreted sorts and functions.
 **/

#include "theory/builtin/type_enumerator.h"

namespace CVC4 {
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

} /* CVC4::theory::builtin namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
