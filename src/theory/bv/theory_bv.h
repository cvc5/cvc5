/*********************                                                        */
/*! \file theory_bv.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan, lianah
 ** Minor contributors (to current version): barrett, ajreynol
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
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
#include "util/statistics_registry.h"
#include "theory/bv/bv_subtheory.h"
#include "theory/bv/bv_subtheory_core.h"
#include "theory/bv/bv_subtheory_bitblast.h"
#include "theory/bv/bv_subtheory_inequality.h"
#include "theory/bv/slicer.h"

namespace CVC4 {
namespace theory {
namespace bv {

class TheoryBV : public Theory {

  /** The context we are using */
  context::Context* d_context;

  /** Context dependent set of atoms we already propagated */
  context::CDHashSet<Node, NodeHashFunction> d_alreadyPropagatedSet;
  context::CDHashSet<Node, NodeHashFunction> d_sharedTermsSet;
  
  CoreSolver       d_coreSolver;
  InequalitySolver d_inequalitySolver; 
  BitblastSolver   d_bitblastSolver;
public:

  TheoryBV(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe);
  ~TheoryBV();

  void setMasterEqualityEngine(eq::EqualityEngine* eq);

  void preRegisterTerm(TNode n);

  void check(Effort e);

  void propagate(Effort e);

  Node explain(TNode n);

  void collectModelInfo( TheoryModel* m, bool fullModel );

  std::string identify() const { return std::string("TheoryBV"); }

  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions);
  Node ppRewrite(TNode t);

  void presolve();
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
  friend class CoreSolver;
  friend class InequalitySolver; 
};/* class TheoryBV */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__THEORY_BV_H */
