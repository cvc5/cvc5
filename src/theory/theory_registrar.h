/*********************                                                        */
/*! \file theory_registrar.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Tim King, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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

#ifndef CVC4__THEORY__THEORY_REGISTRAR_H
#define CVC4__THEORY__THEORY_REGISTRAR_H

#include "prop/registrar.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

class TheoryRegistrar : public prop::Registrar {
private:
  TheoryEngine* d_theoryEngine;

public:

  TheoryRegistrar(TheoryEngine* te) : d_theoryEngine(te) { }

  void preRegister(Node n) override { d_theoryEngine->preRegister(n); }

};/* class TheoryRegistrar */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__THEORY_REGISTRAR_H */
