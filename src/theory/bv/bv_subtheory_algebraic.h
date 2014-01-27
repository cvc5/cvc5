/*********************                                                        */
/*! \file bv_subtheory_bitblast.h
 ** \verbatim
 ** Original author: Liana Hadarean 
 ** Major contributors: none
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

#pragma once

#include "theory/bv/bv_subtheory.h"
#include "theory/bv/bitblaster_template.h"

namespace CVC4 {
namespace theory {
namespace bv {

class BVQuickCheck;

/**
 * AlgebraicSolver
 */
class AlgebraicSolver : public SubtheorySolver {
  struct Statistics {
    IntStat d_numCallstoCheck;
    Statistics();
    ~Statistics();
  };
  /** Bitblaster */
  BVQuickCheck* d_quickSolver;

public:
  AlgebraicSolver(context::Context* c, TheoryBV* bv);
  ~AlgebraicSolver();

  void  preRegister(TNode node) {}
  bool  check(Theory::Effort e);
  void  explain(TNode literal, std::vector<TNode>& assumptions) {Unreachable("AlgebraicSolver does not propagate.\n");}
  EqualityStatus getEqualityStatus(TNode a, TNode b) { Unreachable();}
  void collectModelInfo(TheoryModel* m, bool fullModel) { Unreachable(); }
  Node getModelValue(TNode node) { Unreachable(); }
  bool isComplete();
};

}
}
}
