/*********************                                                        */
/** node.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Reference-counted encapsulation of a pointer to node information.
 **/

#include "expr/node.h"
#include "util/output.h"

namespace CVC4 {
namespace expr {

#ifdef CVC4_DEBUG

/**
 * Pretty printer for use within gdb.  This is not intended to be used
 * outside of gdb.  This writes to the Warning() stream and immediately
 * flushes the stream.
 *
 * Note that this function cannot be a template, since the compiler
 * won't instantiate it.  Even if we explicitly instantiate.  (Odd?)
 * So we implement twice.
 */
void CVC4_PUBLIC debugPrint(const NodeTemplate<true>& n) {
  n.printAst(Warning(), 0);
  Warning().flush();
}

void CVC4_PUBLIC debugPrint(const NodeTemplate<false>& n) {
  n.printAst(Warning(), 0);
  Warning().flush();
}

#endif /* CVC4_DEBUG */

}/* CVC4::expr namespace */
}/* CVC4 namespace */
