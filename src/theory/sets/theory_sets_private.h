/*********************                                                        */
/*! \file theory_sets_private.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Sets theory implementation.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H
#define CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H

#include "context/cdhashset.h"
#include "context/cdqueue.h"
#include "expr/node_trie.h"
#include "theory/sets/cardinality_extension.h"
#include "theory/sets/sets_state.h"
#include "theory/sets/theory_sets_rels.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace sets {

/** Internal classes, forward declared here */
class TheorySetsTermInfoManager;
class TheorySets;
class TheorySetsScrutinize;

class TheorySetsPrivate {
  friend class CardinalityExtension;
  friend class SetsState;
  typedef context::CDHashMap< Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashMap< Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
  typedef context::CDHashMap< Node, Node, NodeHashFunction > NodeMap;

 public:
  void eqNotifyNewClass(TNode t);
  void eqNotifyPreMerge(TNode t1, TNode t2);
  void eqNotifyPostMerge(TNode t1, TNode t2);
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);

 private:
  /** Are a and b trigger terms in the equality engine that may be disequal? */
  bool areCareDisequal(Node a, Node b);
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
  void checkSubtypes( std::vector< Node >& lemmas );
  void checkDownwardsClosure( std::vector< Node >& lemmas );
  void checkUpwardsClosure( std::vector< Node >& lemmas );
  void checkDisequalities( std::vector< Node >& lemmas );
  
  void flushLemmas( std::vector< Node >& lemmas, bool preprocess = false );
  void flushLemma( Node lem, bool preprocess = false );
  bool hasLemmaCached( Node lem );
  bool hasProcessed();

  void addCarePairs(TNodeTrie* t1,
                    TNodeTrie* t2,
                    unsigned arity,
                    unsigned depth,
                    unsigned& n_pairs);

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

  /** sent lemma
   *
   * This flag is set to true during a full effort check if this theory
   * called d_out->lemma(...).
   */
  bool d_sentLemma;
  /** added fact
   *
   * This flag is set to true during a full effort check if this theory
   * added an internal fact to its equality engine.
   */
  bool d_addedFact;
  /** full check incomplete
   *
   * This flag is set to true during a full effort check if this theory
   * is incomplete for some reason (for instance, if we combine cardinality
   * with a relation or extended function kind).
   */
  bool d_full_check_incomplete;
  NodeSet d_lemmas_produced;
  std::map< Node, TypeNode > d_most_common_type;
  std::map< Node, Node > d_most_common_type_term;

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
  
  bool needsCheckLastEffort();

  bool collectModelInfo(TheoryModel* m);

  void computeCareGraph();

  Node explain(TNode);

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  void preRegisterTerm(TNode node);

  /** expandDefinition
   * If the sets-ext option is not set and we have an extended operator, 
   * we throw an exception. This function is a no-op otherwise.
   *
   * This is related to github issue #1076
   * TheorySets uses expandDefinition as an entry point to see if the input
   * contains extended operators.
   *
   * We need to be notified when a universe set occurs in our input,
   * before preprocessing and simplification takes place. Otherwise the models
   * may be inaccurate when setsExt is false, here is an example:
   *
   * x,y : (Set Int)
   * x = (as univset (Set Int));
   * 0 in y;
   * check-sat;
   *
   * If setsExt is enabled, the model value of (as univset (Set Int)) is always accurate.
   *
   * If setsExt is not enabled, the following can happen for the above example:
   * x = (as univset (Set Int)) is made into a model substitution during 
   * simplification. This means (as univset (Set Int)) is not a term in any assertion, 
   * and hence we do not throw an exception, nor do we infer that 0 is a member of 
   * (as univset (Set Int)). We instead report a model where x = {}. The correct behavior 
   * is to throw an exception that says universe set is not supported when setsExt disabled.
   * Hence we check for the existence of universe set before simplification here.
   *
   * Another option to fix this is to make TheoryModel::getValue more general
   * so that it makes theory-specific calls to evaluate interpreted symbols.
   */
  Node expandDefinition(LogicRequest &logicRequest, Node n);

  Theory::PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions);
  
  void presolve();

  void propagate(Theory::Effort);

  /** get default output channel */
  OutputChannel* getOutputChannel();
  /** get the valuation */
  Valuation& getValuation();

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
    bool eqNotifyTriggerEquality(TNode equality, bool value) override;
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override;
    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override;
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override;
    void eqNotifyNewClass(TNode t) override;
    void eqNotifyPreMerge(TNode t1, TNode t2) override;
    void eqNotifyPostMerge(TNode t1, TNode t2) override;
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override;
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
  /** Is formula n entailed to have polarity pol in the current context? */
  bool isEntailed(Node n, bool pol) { return d_state.isEntailed(n, pol); }
  /** Is x entailed to be a member of set s in the current context? */
  bool isMember(Node x, Node s);

 private:
  /** The state of the sets solver at full effort */
  SetsState d_state;
  /** subtheory solver for the theory of relations */
  std::unique_ptr<TheorySetsRels> d_rels;
  /** subtheory solver for the theory of sets with cardinality */
  std::unique_ptr<CardinalityExtension> d_cardSolver;
  /** are relations enabled?
   *
   * This flag is set to true during a full effort check if any constraint
   * involving relational constraints is asserted to this theory.
   */
  bool d_rels_enabled;
  /** is cardinality enabled?
   *
   * This flag is set to true during a full effort check if any constraint
   * involving cardinality constraints is asserted to this theory.
   */
  bool d_card_enabled;
};/* class TheorySetsPrivate */


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H */
