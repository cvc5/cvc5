/*********************                                                        */
/*! \file theory_bv.h
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
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__THEORY_BV_H
#define __CVC4__THEORY__BV__THEORY_BV_H

#include "theory/theory.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/stats.h"

namespace BVMinisat {
class SimpSolver; 
}


namespace CVC4 {
namespace theory {
namespace bv {

/// forward declarations 
class Bitblaster;

class TheoryBV : public Theory {

public:

private:

  /** The context we are using */
  context::Context* d_context;

  /** The asserted stuff */
  context::CDList<TNode> d_assertions;
  
  /** Bitblaster */
  Bitblaster* d_bitblaster; 
  Node d_true;
    
public:

  TheoryBV(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation);
  ~TheoryBV(); 

  void preRegisterTerm(TNode n);

  //void registerTerm(TNode n) { }

  void check(Effort e);

  void propagate(Effort e) { }

  Node explain(TNode n);

  Node getValue(TNode n);

  std::string identify() const { return std::string("TheoryBV"); }

  //Node preprocessTerm(TNode term);
  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions); 
private:
  
  class Statistics {
  public:
    AverageStat d_avgConflictSize;
    IntStat     d_solveSubstitutions;
    TimerStat   d_solveTimer;  
    Statistics();
    ~Statistics(); 
  }; 
  
  Statistics d_statistics;
  
};/* class TheoryBV */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__THEORY_BV_H */
