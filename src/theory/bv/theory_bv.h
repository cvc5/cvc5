/*********************                                                        */
/*! \file theory_bv.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__THEORY_BV_H
#define __CVC4__THEORY__BV__THEORY_BV_H

#include <unordered_map>
#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "theory/bv/bv_subtheory.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory.h"
#include "util/hash.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace bv {

class CoreSolver;
class InequalitySolver;
class AlgebraicSolver;
class BitblastSolver;

class EagerBitblastSolver;

class AbstractionModule;

class TheoryBV : public Theory {

  /** The context we are using */
  context::Context* d_context;

  /** Context dependent set of atoms we already propagated */
  context::CDHashSet<Node, NodeHashFunction> d_alreadyPropagatedSet;
  context::CDHashSet<Node, NodeHashFunction> d_sharedTermsSet;

  std::vector<SubtheorySolver*> d_subtheories;
  std::unordered_map<SubTheory, SubtheorySolver*, std::hash<int> > d_subtheoryMap;

public:

  TheoryBV(context::Context* c, context::UserContext* u, OutputChannel& out,
           Valuation valuation, const LogicInfo& logicInfo,
           std::string name = "");

  ~TheoryBV();

  void setMasterEqualityEngine(eq::EqualityEngine* eq);

  Node expandDefinition(LogicRequest &logicRequest, Node node);

  void mkAckermanizationAssertions(std::vector<Node>& assertions);

  void preRegisterTerm(TNode n);

  void check(Effort e);
  
  bool needsCheckLastEffort();

  void propagate(Effort e);

  Node explain(TNode n);

  void collectModelInfo( TheoryModel* m );

  std::string identify() const { return std::string("TheoryBV"); }

  /** equality engine */
  eq::EqualityEngine * getEqualityEngine();
  bool getCurrentSubstitution( int effort, std::vector< Node >& vars, std::vector< Node >& subs, std::map< Node, std::vector< Node > >& exp );
  int getReduction( int effort, Node n, Node& nr );
  
  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions);

  void enableCoreTheorySlicer();

  Node ppRewrite(TNode t);

  void ppStaticLearn(TNode in, NodeBuilder<>& learned);

  void presolve();

  bool applyAbstraction(const std::vector<Node>& assertions, std::vector<Node>& new_assertions);

  void setProofLog( BitVectorProof * bvp );

private:

  class Statistics {
  public:
    AverageStat d_avgConflictSize;
    IntStat     d_solveSubstitutions;
    TimerStat   d_solveTimer;
    IntStat     d_numCallsToCheckFullEffort;
    IntStat     d_numCallsToCheckStandardEffort;
    TimerStat   d_weightComputationTimer;
    IntStat     d_numMultSlice;
    Statistics(const std::string &name);
    ~Statistics();
  };

  Statistics d_statistics;

  void spendResource(unsigned ammount) throw(UnsafeInterruptException);

  /**
   * Return the uninterpreted function symbol corresponding to division-by-zero
   * for this particular bit-width
   * @param k should be UREM or UDIV
   * @param width
   *
   * @return
   */
  Node getBVDivByZero(Kind k, unsigned width);

  typedef std::unordered_set<TNode, TNodeHashFunction> TNodeSet;
  void collectFunctionSymbols(TNode term, TNodeSet& seen);
  void storeFunction(TNode func, TNode term);
  typedef std::unordered_set<Node, NodeHashFunction> NodeSet;
  NodeSet d_staticLearnCache;

  /**
   * Maps from bit-vector width to division-by-zero uninterpreted
   * function symbols.
   */
  std::unordered_map<unsigned, Node> d_BVDivByZero;
  std::unordered_map<unsigned, Node> d_BVRemByZero;


  typedef std::unordered_map<Node, NodeSet, NodeHashFunction>  FunctionToArgs;
  typedef std::unordered_map<Node, Node, NodeHashFunction>  NodeToNode;
  // for ackermanization
  FunctionToArgs d_funcToArgs;
  CVC4::theory::SubstitutionMap d_funcToSkolem;

  context::CDO<bool> d_lemmasAdded;

  // Are we in conflict?
  context::CDO<bool> d_conflict;

  // Invalidate the model cache if check was called
  context::CDO<bool> d_invalidateModelCache;

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

  EagerBitblastSolver* d_eagerSolver;
  AbstractionModule* d_abstractionModule;
  bool d_isCoreTheory;
  bool d_calledPreregister;
  
  //for extended functions
  bool d_needsLastCallCheck;
  context::CDHashSet<Node, NodeHashFunction> d_extf_range_infer;
  context::CDHashSet<Node, NodeHashFunction> d_extf_collapse_infer;
  bool doExtfInferences( std::vector< Node >& terms );
  bool doExtfReductions( std::vector< Node >& terms );
  
  bool wasPropagatedBySubtheory(TNode literal) const {
    return d_propagatedBy.find(literal) != d_propagatedBy.end();
  }

  SubTheory getPropagatingSubtheory(TNode literal) const {
    Assert(wasPropagatedBySubtheory(literal));
    PropagatedMap::const_iterator find = d_propagatedBy.find(literal);
    return (*find).second;
  }

  /** Should be called to propagate the literal.  */
  bool storePropagation(TNode literal, SubTheory subtheory);

  /**
   * Explains why this literal (propagated by subtheory) is true by adding assumptions.
   */
  void explain(TNode literal, std::vector<TNode>& assumptions);

  void addSharedTerm(TNode t);

  bool isSharedTerm(TNode t) { return d_sharedTermsSet.contains(t); }

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  Node getModelValue(TNode var);

  inline std::string indent()
  {
    std::string indentStr(getSatContext()->getLevel(), ' ');
    return indentStr;
  }

  void setConflict(Node conflict = Node::null());

  bool inConflict() {
    return d_conflict;
  }

  void sendConflict();

  void lemma(TNode node) { d_out->lemma(node, RULE_CONFLICT); d_lemmasAdded = true; }

  void checkForLemma(TNode node);

  friend class LazyBitblaster;
  friend class TLazyBitblaster;
  friend class EagerBitblaster;
  friend class BitblastSolver;
  friend class EqualitySolver;
  friend class CoreSolver;
  friend class InequalitySolver;
  friend class AlgebraicSolver;
  friend class EagerBitblastSolver;
};/* class TheoryBV */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__THEORY_BV_H */
