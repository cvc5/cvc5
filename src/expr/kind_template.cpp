/*********************                                                        */
/*! \file kind_template.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Christopher L. Conway, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "expr/kind.h"

namespace CVC4 {
namespace kind {

const char* toString(CVC4::Kind k)
{
  using namespace CVC4::kind;

  switch (k)
  {
    /* special cases */
    case UNDEFINED_KIND: return "UNDEFINED_KIND";
    case NULL_EXPR: return "NULL";
    ${kind_printers}
    case LAST_KIND: return "LAST_KIND";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, CVC4::Kind k)
{
  out << toString(k);
  return out;
}

/** Returns true if the given kind is associative. This is used by ExprManager to
 * decide whether it's safe to modify big expressions by changing the grouping of
 * the arguments. */
/* TODO: This could be generated. */
bool isAssociative(::CVC4::Kind k) {
  switch(k) {
  case kind::AND:
  case kind::OR:
  case kind::MULT:
  case kind::PLUS:
    return true;

  default:
    return false;
  }
}

std::string kindToString(::CVC4::Kind k) {
  std::stringstream ss;
  ss << k;
  return ss.str();
}

}/* CVC4::kind namespace */

std::ostream& operator<<(std::ostream& out, TypeConstant typeConstant) {
  switch(typeConstant) {
${type_constant_descriptions}
  default:
    out << "UNKNOWN_TYPE_CONSTANT";
    break;
  }
  return out;
}

namespace theory {

TheoryId kindToTheoryId(::CVC4::Kind k) {
  switch(k) {
  case kind::UNDEFINED_KIND:
  case kind::NULL_EXPR:
    break;
${kind_to_theory_id}
  case kind::LAST_KIND:
    break;
  }
  throw IllegalArgumentException("", "k", __PRETTY_FUNCTION__, "bad kind");
}

TheoryId typeConstantToTheoryId(::CVC4::TypeConstant typeConstant)
{
  switch (typeConstant)
  {
${type_constant_to_theory_id}
    case LAST_TYPE: break;
  }
  throw IllegalArgumentException(
      "", "k", __PRETTY_FUNCTION__, "bad type constant");
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
