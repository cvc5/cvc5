/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Template for the Type properties header.
 */

#include "cvc5_private.h"

#ifndef CVC5__TYPE_PROPERTIES_H
#define CVC5__TYPE_PROPERTIES_H

#include <sstream>

#include "base/check.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "expr/type_node.h"
#include "options/language.h"

// clang-format off
${type_properties_includes}
// clang-format on

namespace cvc5::internal {
namespace kind {

/**
 * Return the cardinality of the type constant represented by the
 * TypeConstant argument.  This function is auto-generated from Theory
 * "kinds" files, so includes contributions from each theory regarding
 * that theory's types.
 */
inline Cardinality getCardinality(TypeConstant tc)
{
  switch (tc)
  {
    // clang-format off
${type_constant_cardinalities}
      // clang-format on
    default: InternalError() << "No cardinality known for type constant " << tc;
  }
} /* getCardinality(TypeConstant) */

/**
 * Return the cardinality of the type represented by the TypeNode
 * argument.  This function is auto-generated from Theory "kinds"
 * files, so includes contributions from each theory regarding that
 * theory's types.
 */
inline Cardinality getCardinality(TypeNode typeNode) {
  AssertArgument(!typeNode.isNull(), typeNode);
  switch(Kind k = typeNode.getKind()) {
  case TYPE_CONSTANT:
    return getCardinality(typeNode.getConst<TypeConstant>());
    // clang-format off
${type_cardinalities}
    // clang-format on
  default:
    InternalError() << "A theory kinds file did not provide a cardinality "
                    << "or cardinality computer for type:\n"
                    << typeNode << "\nof kind " << k;
  }
}/* getCardinality(TypeNode) */

inline bool isWellFounded(TypeConstant tc) {
  switch(tc) {
    // clang-format off
${type_constant_wellfoundednesses}
    // clang-format on
    default:
      InternalError() << "No well-foundedness status known for type constant: "
                      << tc;
  }
}/* isWellFounded(TypeConstant) */

inline bool isWellFounded(TypeNode typeNode) {
  AssertArgument(!typeNode.isNull(), typeNode);
  switch(Kind k = typeNode.getKind()) {
  case TYPE_CONSTANT:
    return isWellFounded(typeNode.getConst<TypeConstant>());
    // clang-format off
${type_wellfoundednesses}
    // clang-format on
  default:
    InternalError() << "A theory kinds file did not provide a well-foundedness "
                    << "or well-foundedness computer for type:\n"
                    << typeNode << "\nof kind " << k;
  }
}/* isWellFounded(TypeNode) */

Node mkGroundTerm(TypeConstant tc);
Node mkGroundTerm(TypeNode typeNode);

}  // namespace kind
}  // namespace cvc5::internal

#endif /* CVC5__TYPE_PROPERTIES_H */
