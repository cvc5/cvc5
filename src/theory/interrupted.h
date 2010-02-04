/*********************                                           -*- C++ -*-  */
/** interrupted.h
 ** Original author: 
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** The theory output channel interface.
 **/

#ifndef __CVC4__THEORY__INTERRUPTED_H
#define __CVC4__THEORY__INTERRUPTED_H

#include "util/exception.h"

namespace CVC4 {
namespace theory {

class CVC4_PUBLIC Interrupted : public CVC4::Exception {
public:

  // Constructors
  Interrupted() : CVC4::Exception("CVC4::Theory::Interrupted") {}
  Interrupted(const std::string& msg) : CVC4::Exception(msg) {}
  Interrupted(const char* msg) : CVC4::Exception(msg) {}

};/* class Interrupted */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__INTERRUPTED_H */
