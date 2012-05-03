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
#include "context/cdhashset.h"

namespace CVC4 {
namespace theory {
namespace uf {

class TheoryUF : public Theory {
public:

  class NotifyClass {
    TheoryUF& d_uf;
  public:
    NotifyClass(TheoryUF& uf): d_uf(uf) {}

    bool notify(TNode propagation) {
      Debug("uf") << "NotifyClass::notify(" << propagation << ")" << std::endl;
      // Just forward to uf
      return d_uf.propagate(propagation);
    }
    
    void notify(TNode t1, TNode t2) {
      Debug("uf") << "NotifyClass::notify(" << t1 << ", " << t2 << ")" << std::endl;
      Node equality = Rewriter::rewriteEquality(theory::THEORY_UF, t1.eqNode(t2));
      d_uf.propagate(equality);
    }
  };

private:

  /** The notify class */
  NotifyClass d_notify;

  /** Equaltity engine */
  EqualityEngine<NotifyClass> d_equalityEngine;

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
  context::CDList<Node> d_literalsToPropagate;

  /** Index of the next literal to propagate */
  context::CDO<unsigned> d_literalsToPropagateIndex;

  /** All the function terms that the theory has seen */
  context::CDList<TNode> d_functionsTerms;

  /** True node for predicates = true */
  Node d_true;

  /** True node for predicates = false */
  Node d_false;

  /** Symmetry analyzer */
  SymmetryBreaker d_symb;

public:

  /** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
  TheoryUF(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo);

  void check(Effort);
  void propagate(Effort);
  void preRegisterTerm(TNode term);
  Node explain(TNode n);

  void ppStaticLearn(TNode in, NodeBuilder<>& learned);
  void presolve();

  void addSharedTerm(TNode n);
  void computeCareGraph();

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  std::string identify() const {
    return "THEORY_UF";
  }

};/* class TheoryUF */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__THEORY_UF_H */
