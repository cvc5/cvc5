/*********************                                                        */
/*! \file registrar.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Class to encapsulate preregistration duties
 **
 ** Class to encapsulate preregistration duties.  This class permits the
 ** CNF stream implementation to reach into the theory engine to
 ** preregister only those terms with an associated SAT literal (at the
 ** point when they get the SAT literal), without having to refer to the
 ** TheoryEngine class directly.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__REGISTRAR_H
#define __CVC4__THEORY__REGISTRAR_H

#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

class Registrar {
private:
  TheoryEngine* d_theoryEngine;

public:

  Registrar(TheoryEngine* te) : d_theoryEngine(te) { }

  void preRegister(Node n) {
    d_theoryEngine->preRegister(n);
  }

};/* class Registrar */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__REGISTRAR_H */
