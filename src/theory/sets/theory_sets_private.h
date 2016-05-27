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
#include "theory/sets/term_info.h"

namespace CVC4 {
namespace theory {
namespace sets {

/** Internal classes, forward declared here */
class TheorySetsTermInfoManager;
class TheorySets;
class TheorySetsScrutinize;

class TheorySetsPrivate {
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

  Node getModelValue(TNode);

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
    void eqNotifyNewClass(TNode t) {}
    void eqNotifyPreMerge(TNode t1, TNode t2) {}
    void eqNotifyPostMerge(TNode t1, TNode t2) {}
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {}
  } d_notify;

  /** Equality engine */
  eq::EqualityEngine d_equalityEngine;

  /** True and false constant nodes */
  Node d_trueNode;
  Node d_falseNode;

  context::CDO<bool> d_conflict;
  Node d_conflictNode;

  /** Proagate out to output channel */
  bool propagate(TNode);

  /** generate and send out conflict node */
  void conflict(TNode, TNode);

  /** send out a lemma */
  enum SetsLemmaTag {
    SETS_LEMMA_DISEQUAL,
    SETS_LEMMA_MEMBER,
    SETS_LEMMA_GRAPH,
    SETS_LEMMA_OTHER
  };

  /**
   * returns true if a lemmas was generated
   * returns false otherwise (found in cache)
   */
  bool lemma(Node n, SetsLemmaTag t);

  class TermInfoManager {
    TheorySetsPrivate& d_theory;
    context::Context* d_context;
    eq::EqualityEngine* d_eqEngine;
  public:
    CDNodeSet d_terms;
  private:
    std::hash_map<TNode, TheorySetsTermInfo*, TNodeHashFunction> d_info;

    void mergeLists(CDTNodeList* la, const CDTNodeList* lb) const;
    void pushToSettermPropagationQueue(TNode x, TNode S, bool polarity);
    void pushToSettermPropagationQueue(CDTNodeList* l, TNode S, bool polarity);
    void pushToSettermPropagationQueue(TNode x, CDTNodeList* l, bool polarity);
  public:
    TermInfoManager(TheorySetsPrivate&,
                    context::Context* satContext,
                    eq::EqualityEngine*);
    ~TermInfoManager();
    void notifyMembership(TNode fact);
    const CDTNodeList* getParents(TNode x);
    const CDTNodeList* getMembers(TNode S);
    Node getModelValue(TNode n);
    const CDTNodeList* getNonMembers(TNode S);
    void addTerm(TNode n);
    void mergeTerms(TNode a, TNode b);
  };
  TermInfoManager* d_termInfoManager;

  /******
   * Card Vars :
   *
   * mapping from set terms to correpsonding cardinality variable
   * 
   * in the ::check function, when we get one of those cardinality
   * variables to be assigned to 0, we will assert in equality engine
   * to be equal to empty set.
   *
   * if required, we will add more filters so it doesn't leak to
   * outside world
   */
  Node getCardVar(TNode n);
  Node newCardVar(TNode n);
  bool isCardVar(TNode n);
  typedef std::hash_map <Node, Node, NodeHashFunction> NodeNodeHashMap;
  NodeNodeHashMap d_setTermToCardVar;
  NodeNodeHashMap d_cardVarToSetTerm;
  
  /** Assertions and helper functions */
  bool present(TNode atom);
  bool holds(TNode lit) {
    bool polarity = lit.getKind() == kind::NOT ? false : true;
    TNode atom = polarity ? lit : lit[0];
    return holds(atom, polarity);
  }
  bool holds(TNode atom, bool polarity);

  void assertEquality(TNode fact, TNode reason, bool learnt);
  void assertMemebership(TNode fact, TNode reason, bool learnt);

  /** Propagation / learning and helper functions. */
  context::CDQueue< std::pair<Node, Node> > d_propagationQueue;
  context::CDQueue< std::pair<TNode, TNode> > d_settermPropagationQueue;

  void doSettermPropagation(TNode x, TNode S);
  void registerReason(TNode reason, bool save);
  void learnLiteral(TNode atom, bool polarity, Node reason);
  void learnLiteral(TNode lit, Node reason) {
    if(lit.getKind() == kind::NOT) {
      learnLiteral(lit[0], false, reason);
    } else {
      learnLiteral(lit, true, reason);
    }
  }
  void finishPropagation();

  // for any nodes we need to save, because others use TNode
  context::CDHashSet <Node, NodeHashFunction> d_nodeSaver;

  /** Lemmas and helper functions */
  context::CDQueue <Node> d_pending;
  context::CDQueue <Node> d_pendingDisequal;
  context::CDHashSet <Node, NodeHashFunction> d_pendingEverInserted;

  void addToPending(Node n);
  bool isComplete();
  Node getLemma();

  /** model generation and helper function */
  typedef std::set<TNode> Elements;
  typedef std::hash_map<TNode, Elements, TNodeHashFunction> SettermElementsMap;
  const Elements& getElements(TNode setterm, SettermElementsMap& settermElementsMap) const;
  Node elementsToShape(Elements elements, TypeNode setType) const;
  Node elementsToShape(std::set<Node> elements, TypeNode setType) const;
  bool checkModel(const SettermElementsMap& settermElementsMap, TNode S) const;

  context::CDHashMap <Node, Node, NodeHashFunction> d_modelCache;


  // sharing related
  context::CDO<unsigned>  d_ccg_i, d_ccg_j;

  // more debugging stuff
  friend class TheorySetsScrutinize;
  TheorySetsScrutinize* d_scrutinize;
  void dumpAssertionsHumanified() const;  /** do some formatting to make them more readable */



  /***** Cardinality handling *****/
  bool d_cardEnabled;
  void enableCard();
  void cardCreateEmptysetSkolem(TypeNode t);
  
  CDNodeSet d_cardTerms;
  std::set<TypeNode> d_typesAdded;
  CDNodeSet d_processedCardTerms;
  std::map<std::pair<Node, Node>, bool> d_processedCardPairs;
  CDNodeSet d_cardLowerLemmaCache;
  void registerCard(TNode);
  void processCard(Theory::Effort level);

  /* Graph handling */
  std::map<TNode, std::set<TNode> > edgesFd;
  std::map<TNode, std::set<TNode> > edgesBk;
  std::set< std::pair<TNode, TNode> > disjoint;
  std::set<TNode> leaves;
  void buildGraph();

  /* For calculus as in paper */
  void processCard2(Theory::Effort level);
  CDNodeSet d_V;
  context::CDHashMap <TNode, std::vector<TNode>, TNodeHashFunction > d_E;
  void add_edges(TNode source, TNode dest);
  void add_edges(TNode source, TNode dest1, TNode dest2);
  void add_edges(TNode source, TNode dest1, TNode dest2, TNode dest3);
  void add_edges(TNode source, const std::vector<TNode>& dests);
  void add_node(TNode vertex);
  void merge_nodes(std::set<TNode> a, std::set<TNode> b, Node reason);
  std::set<TNode> get_leaves(Node vertex);
  std::set<TNode> get_leaves(Node vertex1, Node vertex2);
  std::set<TNode> get_leaves(Node vertex1, Node vertex2, Node vertex3);
  std::set<TNode> non_empty(std::set<TNode> vertices);
  void print_graph();
  context::CDQueue < std::pair<TNode, TNode> > d_graphMergesPending;
  context::CDList<Node> d_allSetEqualitiesSoFar;
  Node eqSoFar();
  Node eqemptySoFar();

  std::set<TNode> getNonEmptyLeaves(TNode);
  CDNodeSet d_lemmasGenerated;
  bool d_newLemmaGenerated;

  void guessLeavesEmptyLemmas();


  /** relevant terms */
  CDNodeSet d_relTerms;
};/* class TheorySetsPrivate */


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H */
