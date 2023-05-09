/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include <sstream>

#include "expr/kind.h"
#include "printer/printer.h"

namespace cvc5::internal {
namespace kind {

const char* toString(cvc5::internal::Kind k)
{
  using namespace cvc5::internal::kind;

  switch (k)
  {
    /* special cases */
    case UNDEFINED_KIND: return "UNDEFINED_KIND";
    case NULL_EXPR: return "NULL";
      // clang-format off
    ${kind_printers}
      // clang-format on
    case LAST_KIND: return "LAST_KIND";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, cvc5::internal::Kind k)
{
  Printer::getPrinter(out)->toStream(out, k);
  return out;
}

/** Returns true if the given kind is associative. This is used by ExprManager to
 * decide whether it's safe to modify big expressions by changing the grouping of
 * the arguments. */
/* TODO: This could be generated. */
bool isAssociative(cvc5::internal::Kind k)
{
  switch(k) {
  case kind::AND:
  case kind::OR:
  case kind::MULT:
  case kind::ADD: return true;

  default:
    return false;
  }
}

std::string kindToString(cvc5::internal::Kind k) { return toString(k); }

}  // namespace kind

const char* toString(TypeConstant tc)
{
  switch (tc)
  {
    // clang-format off
    ${type_constant_descriptions}
      // clang-format on
    default: return "UNKNOWN_TYPE_CONSTANT";
  }
}
std::ostream& operator<<(std::ostream& out, TypeConstant typeConstant)
{
  return out << toString(typeConstant);
}

namespace theory {

TheoryId kindToTheoryId(cvc5::internal::Kind k)
{
  switch (k)
  {
    case kind::UNDEFINED_KIND:
    case kind::NULL_EXPR:
      break;
      // clang-format off
${kind_to_theory_id}
      // clang-format on
    case kind::LAST_KIND: break;
  }
  throw IllegalArgumentException("", "k", __PRETTY_FUNCTION__, "bad kind");
}

TheoryId typeConstantToTheoryId(cvc5::internal::TypeConstant typeConstant)
{
  switch (typeConstant)
  {
    // clang-format off
${type_constant_to_theory_id}
      // clang-format on
    case LAST_TYPE: break;
  }
  throw IllegalArgumentException(
      "", "k", __PRETTY_FUNCTION__, "bad type constant");
}

}  // namespace theory
}  // namespace cvc5::internal
