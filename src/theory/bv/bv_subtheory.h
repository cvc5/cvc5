/*********************                                                        */
/*! \file bv_subtheory.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Andrew Reynolds, Dejan Jovanovic
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__BV_SUBTHEORY_H
#define __CVC4__THEORY__BV__BV_SUBTHEORY_H

#include "context/context.h"
#include "context/cdqueue.h"
#include "theory/uf/equality_engine.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {

class TheoryModel;

namespace bv {

enum SubTheory {
  SUB_CORE = 1,
  SUB_BITBLAST = 2,
  SUB_INEQUALITY = 3
};

inline std::ostream& operator << (std::ostream& out, SubTheory subtheory) {
  switch (subtheory) {
  case SUB_BITBLAST:
    out << "BITBLASTER";
    break;
  case SUB_CORE:
    out << "BV_CORE_SUBTHEORY";
    break;
  case SUB_INEQUALITY:
    out << "BV_INEQUALITY_SUBTHEORY";
  default:
    Unreachable();
    break;
  }
  return out;
}


// forward declaration
class TheoryBV;

typedef context::CDQueue<Node> AssertionQueue;
/**
 * Abstract base class for bit-vector subtheory solvers
 *
 */
class SubtheorySolver {

protected:

  /** The context we are using */
  context::Context* d_context;

  /** The bit-vector theory */
  TheoryBV* d_bv;
  AssertionQueue d_assertionQueue;
  context::CDO<uint32_t>  d_assertionIndex;
public:

  SubtheorySolver(context::Context* c, TheoryBV* bv) :
    d_context(c),
    d_bv(bv),
    d_assertionQueue(c),
    d_assertionIndex(c, 0)
  {}
  virtual ~SubtheorySolver() {}
  virtual bool check(Theory::Effort e) = 0;
  virtual void explain(TNode literal, std::vector<TNode>& assumptions) = 0;
  virtual void preRegister(TNode node) {}
  virtual void propagate(Theory::Effort e) {}
  virtual void collectModelInfo(TheoryModel* m, bool fullModel) = 0;
  virtual Node getModelValue(TNode var) = 0;
  virtual bool isComplete() = 0;
  virtual EqualityStatus getEqualityStatus(TNode a, TNode b) = 0;
  virtual void addSharedTerm(TNode node) {}
  bool done() { return d_assertionQueue.size() == d_assertionIndex; }
  TNode get() {
    Assert (!done());
    TNode res = d_assertionQueue[d_assertionIndex];
    d_assertionIndex = d_assertionIndex + 1;
    return res;
  }
  virtual void assertFact(TNode fact) { d_assertionQueue.push_back(fact); }
};

}
}
}

#endif /* __CVC4__THEORY__BV__BV_SUBTHEORY_H */
