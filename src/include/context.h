/*********************                                           -*- C++ -*-  */
/** context.h
 ** This file is part of the CVC4 prototype.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_CONTEXT_H
#define __CVC4_CONTEXT_H

namespace CVC4 {

class ContextManager {
public:
  void switchContext(Context);
  Context snapshot();
};/* class ContextManager */

class ContextObject {
public:
  void snapshot();
  void restore();
};/* class ContextObject */

}/* CVC4 namespace */

#endif /* __CVC4_CONTEXT_H */
