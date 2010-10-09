/*********************                                                        */
/*! \file theory_bv.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__THEORY_BV_H
#define __CVC4__THEORY__BV__THEORY_BV_H

#include "theory/theory.h"
#include "context/context.h"
#include "context/cdset.h"
#include "equality_engine.h"

namespace CVC4 {
namespace theory {
namespace bv {

class TheoryBV : public Theory {

public:

  class EqualityNotify {
    TheoryBV& d_theoryBV;
  public:
    EqualityNotify(TheoryBV& theoryBV)
    : d_theoryBV(theoryBV) {}

    bool operator () (size_t triggerId) {
      return d_theoryBV.triggerEquality(triggerId);
    }
  };

private:

  /** Equality reasoning engine */
  EqualityEngine<TheoryBV, EqualityNotify> d_eqEngine;

  /** Equality triggers indexed by ids from the equality manager */
  std::vector<Node> d_triggers;

  /** The asserted stuff */
  context::CDSet<TNode, TNodeHashFunction> d_assertions;

  /** Called by the equality managere on triggers */
  bool triggerEquality(size_t triggerId);

public:

  TheoryBV(int id, context::Context* c, OutputChannel& out) :
    Theory(id, c, out), d_eqEngine(*this, c), d_assertions(c) {
  }

  void preRegisterTerm(TNode n);

  void registerTerm(TNode n) { }

  void check(Effort e);

  void propagate(Effort e) {}

  void explain(TNode n, Effort e) { }

  Node getValue(TNode n, TheoryEngine* engine);

  RewriteResponse postRewrite(TNode n, bool topLevel);

  std::string identify() const { return std::string("TheoryBV"); }
};/* class TheoryBV */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__THEORY_BV_H */
