/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Template for the Node kind header.
 */

#include "cvc5_public.h"

#ifndef CVC5__KIND_H
#define CVC5__KIND_H

#include <iosfwd>

#include "base/exception.h"
#include "theory/theory_id.h"

namespace cvc5::internal {
namespace kind {

enum Kind_t
{
  UNDEFINED_KIND = -1, /**< undefined */
  NULL_EXPR,           /**< Null kind */
  // clang-format off
  ${kind_decls} LAST_KIND /**< marks the upper-bound of this enumeration */
  // clang-format on

}; /* enum Kind_t */

}  // namespace kind

// import Kind into the "cvc5" namespace but keep the individual kind
// constants under kind::
typedef cvc5::internal::kind::Kind_t Kind;

namespace kind {

/**
 * Converts an kind to a string. Note: This function is also used in
 * `safe_print()`. Changing this functions name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param k The kind
 * @return The name of the kind
 */
const char* toString(cvc5::internal::Kind k);

/**
 * Writes a kind name to a stream.
 *
 * @param out The stream to write to
 * @param k The kind to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream&, cvc5::internal::Kind);

/** Returns true if the given kind is associative. This is used by ExprManager to
 * decide whether it's safe to modify big expressions by changing the grouping of
 * the arguments. */
/* TODO: This could be generated. */
bool isAssociative(cvc5::internal::Kind k);
std::string kindToString(cvc5::internal::Kind k);

struct KindHashFunction
{
  inline size_t operator()(cvc5::internal::Kind k) const { return k; }
}; /* struct KindHashFunction */

}  // namespace kind

/**
 * The enumeration for the built-in atomic types.
 */
enum TypeConstant
{
  // clang-format off
  ${type_constant_list} LAST_TYPE
  // clang-format on
}; /* enum TypeConstant */

/**
 * We hash the constants with their values.
 */
struct TypeConstantHashFunction
{
  inline size_t operator()(TypeConstant tc) const { return tc; }
}; /* struct TypeConstantHashFunction */

const char* toString(TypeConstant tc);
std::ostream& operator<<(std::ostream& out, TypeConstant typeConstant);

namespace theory {

cvc5::internal::theory::TheoryId kindToTheoryId(cvc5::internal::Kind k);
cvc5::internal::theory::TheoryId typeConstantToTheoryId(
    cvc5::internal::TypeConstant typeConstant);

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__KIND_H */
