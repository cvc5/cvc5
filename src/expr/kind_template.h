/*********************                                                        */
/*! \file kind_template.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Template for the Node kind header.
 **
 ** Template for the Node kind header.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__KIND_H
#define __CVC4__KIND_H

#include <iostream>
#include <sstream>

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
}/* CVC4 namespace */

#endif /* __CVC4__KIND_H */
