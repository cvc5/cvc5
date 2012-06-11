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
#include "context/cdhashset.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/stats.h"
#include "context/cdqueue.h"
#include "theory/bv/bv_subtheory.h"
#include "theory/bv/bv_subtheory_eq.h"
#include "theory/bv/bv_subtheory_bitblast.h"

namespace CVC4 {
namespace theory {
namespace bv {

class TheoryBV : public Theory {

  /** The context we are using */
  context::Context* d_context;

  /** Context dependent set of atoms we already propagated */
  context::CDHashSet<TNode, TNodeHashFunction> d_alreadyPropagatedSet;
  context::CDHashSet<TNode, TNodeHashFunction> d_sharedTermsSet;

  BitblastSolver d_bitblastSolver;
  EqualitySolver d_equalitySolver;
public:

  TheoryBV(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe);
  ~TheoryBV();

  void preRegisterTerm(TNode n);

  void check(Effort e);

  void propagate(Effort e);
  
  Node explain(TNode n);

  Node getValue(TNode n);

  std::string identify() const { return std::string("TheoryBV"); }

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

  // Are we in conflict?
  context::CDO<bool> d_conflict;

  /** The conflict node */
  Node d_conflictNode;

  /** Literals to propagate */
  context::CDList<Node> d_literalsToPropagate;

  /** Index of the next literal to propagate */
  context::CDO<unsigned> d_literalsToPropagateIndex;

  /**
   * Keeps a map from nodes to the subtheory that propagated it so that we can explain it
   * properly.
   */
  typedef context::CDHashMap<Node, SubTheory, NodeHashFunction> PropagatedMap;
  PropagatedMap d_propagatedBy;

  bool propagatedBy(TNode literal, SubTheory subtheory) const {
    PropagatedMap::const_iterator find = d_propagatedBy.find(literal);
    if (find == d_propagatedBy.end()) return false;
    else return (*find).second == subtheory;
  }

  /** Should be called to propagate the literal.  */
  bool storePropagation(TNode literal, SubTheory subtheory);

  /**
   * Explains why this literal (propagated by subtheory) is true by adding assumptions.
   */
  void explain(TNode literal, std::vector<TNode>& assumptions);

  void addSharedTerm(TNode t);

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  inline std::string indent()
  {
    std::string indentStr(getSatContext()->getLevel(), ' ');
    return indentStr;
  }

  void setConflict(Node conflict = Node::null()) {
    d_conflict = true; 
    d_conflictNode = conflict;
  }

  bool inConflict() {
    return d_conflict;
  }

  void sendConflict();

  friend class Bitblaster;
  friend class BitblastSolver;
  friend class EqualitySolver; 
  
};/* class TheoryBV */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__THEORY_BV_H */
