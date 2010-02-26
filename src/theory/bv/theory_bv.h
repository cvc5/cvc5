/*********************                                                        */
/** theory_bv.h
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
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__THEORY_BV_H
#define __CVC4__THEORY__BV__THEORY_BV_H

#include "theory/theory.h"
#include "context/context.h"

namespace CVC4 {
namespace theory {
namespace bv {

class TheoryBV : public TheoryImpl<TheoryBV> {
public:
  TheoryBV(context::Context* c, OutputChannel& out) :
    TheoryImpl<TheoryBV>(c, out) {
  }

  void preRegisterTerm(TNode n) { Unimplemented(); }
  void registerTerm(TNode n) { Unimplemented(); }
  void check(Effort e) { Unimplemented(); }
  void propagate(Effort e) { Unimplemented(); }
  void explain(TNode n, Effort e) { Unimplemented(); }
};

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__THEORY_BV_H */
