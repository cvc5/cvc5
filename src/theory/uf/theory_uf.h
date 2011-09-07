/*********************                                                        */
/*! \file theory_uf.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This is the interface to TheoryUF implementations
 **
 ** This is the interface to TheoryUF implementations.  All
 ** implementations of TheoryUF should inherit from this class.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__UF__THEORY_UF_H
#define __CVC4__THEORY__UF__THEORY_UF_H

#include "expr/node.h"
#include "expr/attribute.h"

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/symmetry_breaker.h"

#include "context/cdo.h"
#include "context/cdset.h"

namespace CVC4 {
namespace theory {
namespace uf {

class TheoryUF : public Theory {
public:

  class NotifyClass {
    TheoryUF& d_uf;
  public:
    NotifyClass(TheoryUF& uf): d_uf(uf) {}

    bool notifyEquality(TNode reason) {
      Debug("uf") << "NotifyClass::notifyEquality(" << reason << ")" << std::endl;
      // Just forward to uf
      return d_uf.propagate(reason);
    }
  };

private:

  /** The notify class */
  NotifyClass d_notify;

  /** Equaltity engine */
  EqualityEngine<NotifyClass> d_equalityEngine;

  /** All the literals known to be true */
  context::CDSet<TNode, TNodeHashFunction> d_knownFacts;

  /** Are we in conflict */
  context::CDO<bool> d_conflict;

  /** The conflict node */
  Node d_conflictNode;

  /**
   * Should be called to propagate the literal. 
   */
  bool propagate(TNode literal);

  /**
   * Explain why this literal is true by adding assumptions
   */
  void explain(TNode literal, std::vector<TNode>& assumptions);

  /** Literals to propagate */
  context::CDList<TNode> d_literalsToPropagate;

  /** Index of the next literal to propagate */
  context::CDO<unsigned> d_literalsToPropagateIndex;


  /** True node for predicates = true */
  Node d_true;

  /** True node for predicates = false */
  Node d_false;

  /** Symmetry analyzer */
  SymmetryBreaker d_symb;

public:

  /** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
  TheoryUF(context::Context* ctxt, OutputChannel& out, Valuation valuation):
    Theory(THEORY_UF, ctxt, out, valuation),
    d_notify(*this),
    d_equalityEngine(d_notify, ctxt, "theory::uf::TheoryUF"),
    d_knownFacts(ctxt),
    d_conflict(ctxt, false),
    d_literalsToPropagate(ctxt),
    d_literalsToPropagateIndex(ctxt, 0)
  {
    // The kinds we are treating as function application in congruence
    d_equalityEngine.addFunctionKind(kind::APPLY_UF);
    d_equalityEngine.addFunctionKind(kind::EQUAL);

    // The boolean constants
    d_true = NodeManager::currentNM()->mkConst<bool>(true);
    d_false = NodeManager::currentNM()->mkConst<bool>(false);
    d_equalityEngine.addTerm(d_true);
    d_equalityEngine.addTerm(d_false);
    d_equalityEngine.addTriggerEquality(d_true, d_false, d_false);
  }

  void check(Effort);
  void propagate(Effort);
  void preRegisterTerm(TNode term);
  void explain(TNode n);

  void staticLearning(TNode in, NodeBuilder<>& learned);
  void presolve();

  std::string identify() const {
    return "THEORY_UF";
  }

};/* class TheoryUF */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__THEORY_UF_H */
