/*********************                                                        */
/*! \file bv_subtheory_bitblast.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): lianah
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

#pragma once

#include "theory/bv/bv_subtheory.h"

namespace CVC4 {
namespace theory {
namespace bv {

class Bitblaster;

/**
 * BitblastSolver
 */
class BitblastSolver : public SubtheorySolver {

  /** Bitblaster */
  Bitblaster* d_bitblaster;

  /** Nodes that still need to be bit-blasted */
  context::CDQueue<TNode> d_bitblastQueue;

public:
  BitblastSolver(context::Context* c, TheoryBV* bv);
  ~BitblastSolver();

  void  preRegister(TNode node);
  bool  addAssertions(const std::vector<TNode>& assertions, Theory::Effort e);
  void  explain(TNode literal, std::vector<TNode>& assumptions);
  EqualityStatus getEqualityStatus(TNode a, TNode b);
  void collectModelInfo(TheoryModel* m); 
};

}
}
}
