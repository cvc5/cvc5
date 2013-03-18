/*********************                                                        */
/*! \file bv_subtheory_inequality.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
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

#ifndef __CVC4__THEORY__BV__BV_SUBTHEORY__INEQUALITY_H
#define __CVC4__THEORY__BV__BV_SUBTHEORY__INEQUALITY_H

#include "theory/bv/theory_bv.h"
#include "theory/bv/bv_subtheory.h"
namespace CVC4 {
namespace theory {


namespace bv {

class InequalitySolver: public SubtheorySolver {

public:
  
  InequalitySolver(context::Context* c, TheoryBV* bv)
    : SubtheorySolver(c, bv)
  {}
  
  bool check(Theory::Effort e);
  void propagate(Theory::Effort e); 
  void explain(TNode literal, std::vector<TNode>& assumptions); 
}; 

}
}
}

#endif /* __CVC4__THEORY__BV__BV_SUBTHEORY__INEQUALITY_H */ 
