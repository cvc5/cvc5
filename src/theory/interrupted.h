/*********************                                                        */
/*! \file interrupted.h
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
 ** \brief The theory output channel interface.
 **
 ** The theory output channel interface.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__INTERRUPTED_H
#define __CVC4__THEORY__INTERRUPTED_H

#include "util/exception.h"

namespace CVC4 {
namespace theory {

class Interrupted : public CVC4::Exception {
};/* class Interrupted */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__INTERRUPTED_H */
