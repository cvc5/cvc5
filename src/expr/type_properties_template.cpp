/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Morgan Deters, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Template for the Type properties source file.
 */

#include "expr/type_properties.h"

namespace cvc5::internal {
namespace kind {

Node mkGroundTerm(TypeConstant tc)
{
  switch (tc)
  {
    // clang-format off
${type_constant_groundterms}
      // clang-format on
    default:
      InternalError() << "No ground term known for type constant: " << tc;
  }
}

Node mkGroundTerm(TypeNode typeNode)
{
  AssertArgument(!typeNode.isNull(), typeNode);
  switch (Kind k = typeNode.getKind())
  {
    case TYPE_CONSTANT:
      return mkGroundTerm(typeNode.getConst<TypeConstant>());
      // clang-format off
${type_groundterms}
      // clang-format on
    default:
      InternalError() << "A theory kinds file did not provide a ground term "
                      << "or ground term computer for type:\n"
                      << typeNode << "\nof kind " << k;
  }
}

}  // namespace kind
}  // namespace cvc5::internal
