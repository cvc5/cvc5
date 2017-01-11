/*********************                                                        */
/*! \file theory_sets_private.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Sets theory implementation.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H
#define __CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H

#include "context/cdhashset.h"
#include "context/cdqueue.h"

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"
#include "theory/sets/theory_sets_rels.h"

namespace CVC4 {
namespace theory {

namespace quantifiers{
  class TermArgTrie;
}

namespace sets {

/** Internal classes, forward declared here */
class TheorySetsTermInfoManager;
class TheorySets;
class TheorySetsScrutinize;

class TheorySetsPrivate {
//new implementation
  typedef context::CDHashMap< Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashMap< Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
  typedef context::CDHashMap< Node, Node, NodeHashFunction > NodeMap;
private:
  TheorySetsRels * d_rels;
public:
  void eqNotifyNewClass(TNode t);
  void eqNotifyPreMerge(TNode t1, TNode t2);
  void eqNotifyPostMerge(TNode t1, TNode t2);
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
private:
  bool ee_areEqual( Node a, Node b );
  bool ee_areDisequal( Node a, Node b );
  NodeIntMap d_members;
  std::map< Node, std::vector< Node > > d_members_data;
  bool assertFact( Node fact, Node exp );
  // inferType : 1 : must send out as lemma, -1 : do internal inferences if possible, 0 : default.
  bool assertFactRec( Node fact, Node exp, std::vector< Node >& lemma, int inferType = 0 );
  // add inferences corresponding to ( exp => fact ) to lemmas, equality engine
  void assertInference( Node fact, Node exp, std::vector< Node >& lemmas, const char * c, int inferType = 0 );
  void assertInference( Node fact, std::vector< Node >& exp, std::vector< Node >& lemmas, const char * c, int inferType = 0 );
  void assertInference( std::vector< Node >& conc, Node exp, std::vector< Node >& lemmas, const char * c, int inferType = 0 );
  void assertInference( std::vector< Node >& conc, std::vector< Node >& exp, std::vector< Node >& lemmas, const char * c, int inferType = 0 );
  // send lemma ( n OR (NOT n) ) immediately
  void split( Node n, int reqPol=0 );
  void fullEffortCheck();
  void checkDownwardsClosure( std::vector< Node >& lemmas );
  void checkUpwardsClosure( std::vector< Node >& lemmas );
  void checkDisequalities( std::vector< Node >& lemmas );
  bool isMember( Node x, Node s );
  bool isSetDisequalityEntailed( Node s, Node t );
  
  void flushLemmas( std::vector< Node >& lemmas );
  Node getProxy( Node n );
  Node getCongruent( Node n );
  Node getEmptySet( TypeNode tn );
  bool hasLemmaCached( Node lem );
  bool hasProcessed();
  
  void addCarePairs( quantifiers::TermArgTrie * t1, quantifiers::TermArgTrie * t2, unsigned arity, unsigned depth, unsigned& n_pairs );
  
  Node d_true;
  Node d_false;
  Node d_zero;
  NodeBoolMap d_deq;
  NodeSet d_deq_processed;
  NodeSet d_keep;
  std::vector< Node > d_emp_exp;
  
  //propagation
  class EqcInfo
  {
  public:
    EqcInfo( context::Context* c );
    ~EqcInfo(){}
    // singleton or emptyset equal to this eqc
    context::CDO< Node > d_singleton;
  };
  /** information necessary for equivalence classes */
  std::map< Node, EqcInfo* > d_eqc_info;
  /** get or make eqc info */
  EqcInfo* getOrMakeEqcInfo( TNode n, bool doMake = false );
  
  void addEqualityToExp( Node a, Node b, std::vector< Node >& exp );
  
  void debugPrintSet( Node s, const char * c );
  
  bool d_sentLemma;
  bool d_addedFact;
  NodeMap d_proxy;  
  NodeMap d_proxy_to_term;  
  NodeSet d_lemmas_produced;
  std::vector< Node > d_set_eqc;
  std::map< Node, std::vector< Node > > d_set_eqc_list;
  std::map< TypeNode, Node > d_eqc_emptyset;
  std::map< Node, Node > d_eqc_singleton;
  std::map< TypeNode, Node > d_emptyset;
  std::map< Node, Node > d_congruent;
  std::map< Node, std::vector< Node > > d_nvar_sets;
  std::map< Node, std::map< Node, Node > > d_pol_mems[2];
  std::map< Node, std::map< Node, Node > > d_members_index;
  std::map< Node, Node > d_singleton_index;
  std::map< Kind, std::map< Node, std::map< Node, Node > > > d_bop_index;
  std::map< Kind, std::vector< Node > > d_op_list;
  //cardinality
private:
  bool d_card_enabled;
  bool d_rels_enabled;
  std::map< Node, Node > d_eqc_to_card_term;
  NodeSet d_card_processed;
  std::map< Node, std::vector< Node > > d_card_parent;
  std::map< Node, std::map< Node, std::vector< Node > > > d_ff;
  std::map< Node, std::vector< Node > > d_nf;
  std::map< Node, Node > d_card_base;
  void checkCardBuildGraph( std::vector< Node >& lemmas );
  void registerCardinalityTerm( Node n, std::vector< Node >& lemmas );
  void checkCardCycles( std::vector< Node >& lemmas );
  void checkCardCyclesRec( Node eqc, std::vector< Node >& curr, std::vector< Node >& exp, std::vector< Node >& lemmas );
  void checkNormalForms( std::vector< Node >& lemmas, std::vector< Node >& intro_sets );
  void checkNormalForm( Node eqc, std::vector< Node >& intro_sets );
  void checkMinCard( std::vector< Node >& lemmas );
public:

  /**
   * Constructs a new instance of TheorySetsPrivate w.r.t. the provided
   * contexts.
   */
  TheorySetsPrivate(TheorySets& external,
                    context::Context* c,
                    context::UserContext* u);

  ~TheorySetsPrivate();

  void setMasterEqualityEngine(eq::EqualityEngine* eq);

  void addSharedTerm(TNode);

  void check(Theory::Effort);

  void collectModelInfo(TheoryModel*, bool fullModel);

  void computeCareGraph();

  Node explain(TNode);

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  void preRegisterTerm(TNode node);

  void presolve();

  void propagate(Theory::Effort);

private:
  TheorySets& d_external;

  class Statistics {
  public:
    TimerStat d_getModelValueTime;
    TimerStat d_mergeTime;
    TimerStat d_processCard2Time;
    IntStat d_memberLemmas;
    IntStat d_disequalityLemmas;
    IntStat d_numVertices;
    IntStat d_numVerticesMax;
    IntStat d_numMergeEq1or2;
    IntStat d_numMergeEq3;
    IntStat d_numLeaves;
    IntStat d_numLeavesMax;

    Statistics();
    ~Statistics();
  } d_statistics;

  /** Functions to handle callbacks from equality engine */
  class NotifyClass : public eq::EqualityEngineNotify {
    TheorySetsPrivate& d_theory;

  public:
    NotifyClass(TheorySetsPrivate& theory): d_theory(theory) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value);
    bool eqNotifyTriggerPredicate(TNode predicate, bool value);
    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value);
    void eqNotifyConstantTermMerge(TNode t1, TNode t2);
    void eqNotifyNewClass(TNode t);
    void eqNotifyPreMerge(TNode t1, TNode t2);
    void eqNotifyPostMerge(TNode t1, TNode t2);
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
  } d_notify;

  /** Equality engine */
  eq::EqualityEngine d_equalityEngine;

  context::CDO<bool> d_conflict;
  Node d_conflictNode;

  /** Proagate out to output channel */
  bool propagate(TNode);

  /** generate and send out conflict node */
  void conflict(TNode, TNode);
  
  bool isCareArg( Node n, unsigned a );
public:
  bool isEntailed( Node n, bool pol );
  
};/* class TheorySetsPrivate */


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H */
