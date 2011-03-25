/*********************                                                        */
/*! \file theory_bool.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory of booleans.
 **
 ** The theory of booleans.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BOOLEANS__THEORY_BOOL_H
#define __CVC4__THEORY__BOOLEANS__THEORY_BOOL_H

#include "theory/theory.h"
#include "context/context.h"

namespace CVC4 {
namespace theory {
namespace booleans {

class TheoryBool : public Theory {
public:
  TheoryBool(context::Context* c, OutputChannel& out, Valuation valuation) :
    Theory(THEORY_BOOL, c, out, valuation) {
  }

  void preRegisterTerm(TNode n) {
    Debug("bool") << "bool: begin preRegisterTerm(" << n << ")" << std::endl;
    Debug("bool") << "bool: end preRegisterTerm(" << n << ")" << std::endl;
  }
  void registerTerm(TNode n) {
    Debug("bool") << "bool: begin preRegisterTerm(" << n << ")" << std::endl;
    Debug("bool") << "bool: end preRegisterTerm(" << n << ")" << std::endl;
  }

  Node getValue(TNode n);

  std::string identify() const { return std::string("TheoryBool"); }
};

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BOOLEANS__THEORY_BOOL_H */
