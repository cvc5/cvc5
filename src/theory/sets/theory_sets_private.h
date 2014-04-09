/*********************                                                        */
/*! \file theory_sets_private.h
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2013-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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

  void addSharedTerm(TNode);

  void check(Theory::Effort);

  void collectModelInfo(TheoryModel*, bool fullModel);

  Node explain(TNode);

  void preRegisterTerm(TNode node);

  void propagate(Theory::Effort) { /* we don't depend on this call */ }

private:
  TheorySets& d_external;

  class Statistics {
  public:
    TimerStat d_checkTime;

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

  context::CDO<bool> d_conflict;
  Node d_conflictNode;

  /** Proagate out to output channel */
  bool propagate(TNode);

  /** generate and send out conflict node */
  void conflict(TNode, TNode);

  class TermInfoManager {
    TheorySetsPrivate& d_theory;
    context::Context* d_context;
    eq::EqualityEngine* d_eqEngine;

    CDNodeSet d_terms;
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
    void addTerm(TNode n);
    void mergeTerms(TNode a, TNode b);
  };
  TermInfoManager* d_termInfoManager;

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
  context::CDQueue <TNode> d_pending;
  context::CDQueue <TNode> d_pendingDisequal;
  context::CDHashSet <Node, NodeHashFunction> d_pendingEverInserted;

  void addToPending(Node n);
  bool isComplete();
  Node getLemma();

  /** model generation and helper function */
  typedef std::set<TNode> Elements;
  typedef std::hash_map<TNode, Elements, TNodeHashFunction> SettermElementsMap;
  const Elements& getElements(TNode setterm, SettermElementsMap& settermElementsMap) const;
  Node elementsToShape(Elements elements, TypeNode setType) const;
  bool checkModel(const SettermElementsMap& settermElementsMap, TNode S) const;

  // more debugging stuff
  friend class TheorySetsScrutinize;
  TheorySetsScrutinize* d_scrutinize;
};/* class TheorySetsPrivate */


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H */
