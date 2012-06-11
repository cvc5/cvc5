/*********************                                                        */
/*! \file kind_template.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Template for the Node kind header
 **
 ** Template for the Node kind header.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__KIND_H
#define __CVC4__KIND_H

#include <iostream>
#include <sstream>

#include "util/Assert.h"

namespace CVC4 {
namespace kind {

enum Kind_t {
  UNDEFINED_KIND = -1, /**< undefined */
  NULL_EXPR, /**< Null kind */
${kind_decls}
  LAST_KIND /**< marks the upper-bound of this enumeration */

};/* enum Kind_t */

}/* CVC4::kind namespace */

// import Kind into the "CVC4" namespace but keep the individual kind
// constants under kind::
typedef ::CVC4::kind::Kind_t Kind;

namespace kind {

inline std::ostream& operator<<(std::ostream&, CVC4::Kind) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& out, CVC4::Kind k) {
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

#line 66 "${template}"

/** Returns true if the given kind is associative. This is used by ExprManager to
 * decide whether it's safe to modify big expressions by changing the grouping of
 * the arguments. */
/* TODO: This could be generated. */
inline bool isAssociative(::CVC4::Kind k) {
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

inline std::string kindToString(::CVC4::Kind k) {
  std::stringstream ss;
  ss << k;
  return ss.str();
}

struct KindHashStrategy {
  static inline size_t hash(::CVC4::Kind k) { return k; }
};/* struct KindHashStrategy */

}/* CVC4::kind namespace */

/**
 * The enumeration for the built-in atomic types.
 */
enum TypeConstant {
${type_constant_list}
  LAST_TYPE
};/* enum TypeConstant */

/**
 * We hash the constants with their values.
 */
struct TypeConstantHashStrategy {
  static inline size_t hash(TypeConstant tc) {
    return tc;
  }
};/* struct BoolHashStrategy */

inline std::ostream& operator<<(std::ostream& out, TypeConstant typeConstant) {
  switch(typeConstant) {
${type_constant_descriptions}
  default:
    out << "UNKNOWN_TYPE_CONSTANT";
    break;
  }
  return out;
}

namespace theory {

enum TheoryId {
${theory_enum}
  THEORY_LAST
};

const TheoryId THEORY_FIRST = static_cast<TheoryId>(0);
const TheoryId THEORY_SAT_SOLVER = THEORY_LAST;

inline TheoryId& operator ++ (TheoryId& id) {
  return id = static_cast<TheoryId>(((int)id) + 1);
}

inline std::ostream& operator<<(std::ostream& out, TheoryId theoryId) {
  switch(theoryId) {
${theory_descriptions}
  default:
    out << "UNKNOWN_THEORY";
    break;
  }
  return out;
}

inline TheoryId kindToTheoryId(::CVC4::Kind k) {
  switch(k) {
${kind_to_theory_id}
  default:
    Unhandled(k);
  }
}

inline TheoryId typeConstantToTheoryId(::CVC4::TypeConstant typeConstant) {
  switch(typeConstant) {
${type_constant_to_theory_id}
  default:
    Unhandled(typeConstant);
  }
}

}/* theory namespace */


}/* CVC4 namespace */

#endif /* __CVC4__KIND_H */
