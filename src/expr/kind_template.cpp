#include "expr/kind.h"

namespace CVC4 {
namespace kind {

std::ostream& operator<<(std::ostream& out, CVC4::Kind k) {
  using namespace CVC4::kind;

  switch(k) {

  /* special cases */
  case UNDEFINED_KIND: out << "UNDEFINED_KIND"; break;
  case NULL_EXPR: out << "NULL"; break;
${kind_printers}
  case LAST_KIND: out << "LAST_KIND"; break;
  default: out << "UNKNOWNKIND!" << int(k); break;
  }

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
#line 51 "${template}"
  default:
    out << "UNKNOWN_TYPE_CONSTANT";
    break;
  }
  return out;
}

namespace theory {

std::ostream& operator<<(std::ostream& out, TheoryId theoryId) {
  switch(theoryId) {
${theory_descriptions}
#line 64 "${template}"
  default:
    out << "UNKNOWN_THEORY";
    break;
  }
  return out;
}

TheoryId kindToTheoryId(::CVC4::Kind k) {
  switch(k) {
  case kind::UNDEFINED_KIND:
  case kind::NULL_EXPR:
    break;
${kind_to_theory_id}
#line 78 "${template}"
  case kind::LAST_KIND:
    break;
  }
  throw IllegalArgumentException("", "k", __PRETTY_FUNCTION__, "bad kind");
}

TheoryId typeConstantToTheoryId(::CVC4::TypeConstant typeConstant) {
  switch(typeConstant) {
${type_constant_to_theory_id}
#line 88 "${template}"
  case LAST_TYPE:
    break;
  }
  throw IllegalArgumentException("", "k", __PRETTY_FUNCTION__, "bad type constant");
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
