/*********************                                                        */
/** theory_arrays.h
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
 ** Theory of arrays.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H
#define __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H

#include "theory/theory.h"
#include "context/context.h"

namespace CVC4 {
namespace theory {
namespace arrays {

class TheoryArrays : public TheoryImpl<TheoryArrays> {
public:
  TheoryArrays(context::Context* c, OutputChannel& out) :
    TheoryImpl<TheoryArrays>(c, out) {
  }

  void preRegisterTerm(TNode n) { Unimplemented(); }
  void registerTerm(TNode n) { Unimplemented(); }
  void check(Effort e) { Unimplemented(); }
  void propagate(Effort e) { Unimplemented(); }
  void explain(TNode n, Effort e) { Unimplemented(); }
};

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H */
