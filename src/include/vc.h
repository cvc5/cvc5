/*********************                                           -*- C++ -*-  */
/** vc.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#ifndef __CVC4_VC_H
#define __CVC4_VC_H

#include "command.h"
#include "expr.h"

/* TODO provide way of querying whether you fall into a fragment /
 * returning what fragment you're in */

// In terms of abstraction, this is below (and provides services to)
// users using the library interface, and also the parser for the main
// CVC4 binary.  It is above (and requires the services of) the Prover
// class.

namespace CVC4 {

/**
 * User-visible (library) interface to CVC4.
 */
class ValidityChecker {
  // on entry to the validity checker interface, need to set up
  // current state (ExprManager::d_current etc.)
public:
  void doCommand(Command);

  void query(Expr);
};

} /* CVC4 namespace */

#endif /* __CVC4_VC_H */
