/*********************                                                        */
/*! \file bv_subtheory.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Interface for bit-vectors sub-solvers.
 **
 ** Interface for bit-vectors sub-solvers.
 **/

#ifndef CVC4__THEORY__BV__BV_SUBTHEORY_H
#define CVC4__THEORY__BV__BV_SUBTHEORY_H

#include "cvc4_private.h"
#include "context/context.h"
#include "context/cdqueue.h"
#include "theory/uf/equality_engine.h"
#include "theory/theory.h"

namespace CVC4 {

namespace proof {
class BitVectorProof;
}

namespace theory {

class TheoryModel;

namespace bv {

enum SubTheory {
  SUB_CORE = 1,
  SUB_BITBLAST = 2,
  SUB_INEQUALITY = 3,
  SUB_ALGEBRAIC = 4
};

inline std::ostream& operator<<(std::ostream& out, SubTheory subtheory) {
  switch (subtheory) {
    case SUB_BITBLAST:
      return out << "BITBLASTER";
    case SUB_CORE:
      return out << "BV_CORE_SUBTHEORY";
    case SUB_INEQUALITY:
      return out << "BV_INEQUALITY_SUBTHEORY";
    case SUB_ALGEBRAIC:
      return out << "BV_ALGEBRAIC_SUBTHEORY";
    default:
      break;
  }
  Unreachable();
}

// forward declaration
class TheoryBV;

using AssertionQueue = context::CDQueue<Node>;

/**
 * Abstract base class for bit-vector subtheory solvers
 *
 */
class SubtheorySolver {
 public:
  SubtheorySolver(context::Context* c, TheoryBV* bv)
      : d_context(c),
        d_bv(bv),
        d_bvp(nullptr),
        d_assertionQueue(c),
        d_assertionIndex(c, 0) {}
  virtual ~SubtheorySolver() {}
  virtual bool check(Theory::Effort e) = 0;
  virtual void explain(TNode literal, std::vector<TNode>& assumptions) = 0;
  virtual void preRegister(TNode node) {}
  virtual void propagate(Theory::Effort e) {}
  virtual bool collectModelInfo(TheoryModel* m, bool fullModel) = 0;
  virtual Node getModelValue(TNode var) = 0;
  virtual bool isComplete() = 0;
  virtual EqualityStatus getEqualityStatus(TNode a, TNode b) = 0;
  virtual void addSharedTerm(TNode node) {}
  bool done() { return d_assertionQueue.size() == d_assertionIndex; }
  TNode get() {
    Assert(!done());
    TNode res = d_assertionQueue[d_assertionIndex];
    d_assertionIndex = d_assertionIndex + 1;
    return res;
  }
  virtual void assertFact(TNode fact) { d_assertionQueue.push_back(fact); }
  virtual void setProofLog(proof::BitVectorProof* bvp) {}
  AssertionQueue::const_iterator assertionsBegin() {
    return d_assertionQueue.begin();
  }
  AssertionQueue::const_iterator assertionsEnd() {
    return d_assertionQueue.end();
  }

 protected:
  /** The context we are using */
  context::Context* d_context;

  /** The bit-vector theory */
  TheoryBV* d_bv;
  /** proof log */
  proof::ResolutionBitVectorProof* d_bvp;
  AssertionQueue d_assertionQueue;
  context::CDO<uint32_t> d_assertionIndex;
}; /* class SubtheorySolver */

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BV__BV_SUBTHEORY_H */
