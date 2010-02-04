/*********************                                           -*- C++ -*-  */
/** kind.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): cconway, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Kinds of Nodes.
 **/

#ifndef __CVC4__KIND_H
#define __CVC4__KIND_H

#include "cvc4_config.h"
#include <iostream>

namespace CVC4 {

// TODO: create this file (?) from theory solver headers so that we
// have a collection of kinds from all.  This file is mainly a
// placeholder for design & development work.

enum Kind {
  /* undefined */
  UNDEFINED_KIND = -1,
  /** Null Kind */
  NULL_EXPR,

  /* built-ins */
  EQUAL,
  ITE,
  SKOLEM,
  VARIABLE,
  APPLY,

  /* propositional connectives */
  FALSE,
  TRUE,

  NOT,

  AND,
  IFF,
  IMPLIES,
  OR,
  XOR,

  /* from arith */
  PLUS,
  MINUS,
  MULT
};/* enum Kind */

inline std::ostream& operator<<(std::ostream&, CVC4::Kind) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& out, CVC4::Kind k) {
  using namespace CVC4;

  switch(k) {

  /* special cases */
  case UNDEFINED_KIND: out << "UNDEFINED_KIND"; break;
  case NULL_EXPR:      out << "NULL";           break;

  case EQUAL:          out << "EQUAL";          break;
  case ITE:            out << "ITE";            break;
  case SKOLEM:         out << "SKOLEM";         break;
  case VARIABLE:       out << "VARIABLE";       break;
  case APPLY:          out << "APPLY";          break;

  /* propositional connectives */
  case FALSE:          out << "FALSE";          break;
  case TRUE:           out << "TRUE";           break;

  case NOT:            out << "NOT";            break;

  case AND:            out << "AND";            break;
  case IFF:            out << "IFF";            break;
  case IMPLIES:        out << "IMPLIES";        break;
  case OR:             out << "OR";             break;
  case XOR:            out << "XOR";            break;

  /* from arith */
  case PLUS:           out << "PLUS";           break;
  case MINUS:          out << "MINUS";          break;
  case MULT:           out << "MULT";           break;

  default:             out << "UNKNOWNKIND!" << int(k); break;
  }

  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__KIND_H */
