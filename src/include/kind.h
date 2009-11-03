/*********************                                           -*- C++ -*-  */
/** kind.h
 ** This file is part of the CVC4 prototype.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_KIND_H
#define __CVC4_KIND_H

namespace CVC4 {

// TODO: create this file (?) from theory solver headers so that we
// have a collection of kinds from all.  This file is mainly a
// placeholder for design & development work.

enum Kind {
  AND,
  OR,
  XOR,
  NOT,
  PLUS,
  MINUS
};/* enum Kind */

}/* CVC4 namespace */

#endif /* __CVC4_KIND_H */
