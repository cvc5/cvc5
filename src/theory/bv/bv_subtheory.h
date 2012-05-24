/*********************                                                        */
/*! \file bv_subtheory.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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
namespace bv {

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

public:
  
  SubtheorySolver(context::Context* c, TheoryBV* bv) :
    d_context(c),
    d_bv(bv)
  {}
  virtual ~SubtheorySolver() {}

  virtual bool  addAssertions(const std::vector<TNode>& assertions, Theory::Effort e) = 0;
  virtual void  explain(TNode literal, std::vector<TNode>& assumptions) = 0;
  virtual void  preRegister(TNode node) {}

}; 

}
}
}

#endif /* __CVC4__THEORY__BV__BV_SUBTHEORY_H */
