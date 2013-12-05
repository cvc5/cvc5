/*********************                                                        */
/*! \file bv_subtheory_bitblast.h
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters, Andrew Reynolds, Liana Hadarean, Clark Barrett
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
namespace CVC4 {
namespace theory {
namespace bv {

class Bitblaster;

/**
 * BitblastSolver
 */
class BitblastSolver : public SubtheorySolver {
  struct Statistics {
    IntStat d_numCallstoCheck;
    Statistics();
    ~Statistics();
  };
  /** Bitblaster */
  Bitblaster* d_bitblaster;

  /** Nodes that still need to be bit-blasted */
  context::CDQueue<TNode> d_bitblastQueue;
  Statistics d_statistics;

  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
  NodeMap d_modelCache;
  context::CDO<bool> d_validModelCache;
  Node getModelValueRec(TNode node);

  bool  d_useSatPropagation;
public:
  BitblastSolver(context::Context* c, TheoryBV* bv);
  ~BitblastSolver();

  void  preRegister(TNode node);
  bool  check(Theory::Effort e);
  void  explain(TNode literal, std::vector<TNode>& assumptions);
  EqualityStatus getEqualityStatus(TNode a, TNode b);
  void collectModelInfo(TheoryModel* m, bool fullModel);
  Node getModelValue(TNode node);
  bool isComplete() { return true; }
  void bitblastQueue();
};

}
}
}
