/*********************                                           -*- C++ -*-  */
/** vc.h
 ** This file is part of the CVC4 prototype.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_VC_H
#define __CVC4_VC_H

/* TODO provide way of querying whether you fall into a fragment /
 * returning what fragment you're in */

namespace CVC4 {

class ValidityChecker {
public:
  void doCommand(Command);
};

} /* CVC4 namespace */

#endif /* __CVC4_VC_H */
