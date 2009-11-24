/*********************                                           -*- C++ -*-  */
/** kind.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#ifndef __CVC4__KIND_H
#define __CVC4__KIND_H

namespace CVC4 {

// TODO: create this file (?) from theory solver headers so that we
// have a collection of kinds from all.  This file is mainly a
// placeholder for design & development work.

enum Kind {
  /* undefined */
  UNDEFINED_KIND = -1,

  /* built-ins */
  EQUAL,
  ITE,
  SKOLEM,
  VARIABLE,

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

}/* CVC4 namespace */

#endif /* __CVC4__KIND_H */
