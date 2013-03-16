/*********************                                                        */
/*! \file bv_subtheory.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
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


const bool d_useEqualityEngine = true;
const bool d_useSatPropagation = true;

// forward declaration 
class TheoryBV; 

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
  context::CDQueue<TNode> d_assertionQueue;
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
  virtual void propagate(Effort e) {}
  virtual void collectModelInfo(TheoryModel* m) = 0;
  bool done() { return d_assertionQueue.size() == d_assertionIndex; }
  TNode get() {
    Assert (!done()); 
    TNode res = d_assertionQueue[d_assertionIndex];
    d_assertionIndex = d_assertionIndex + 1;
    return res; 
  }
  void assertFact(TNode fact) { d_assertionQueue.push_back(fact); }

}; 

}
}
}

#endif /* __CVC4__THEORY__BV__BV_SUBTHEORY_H */
