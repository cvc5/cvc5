/*********************                                                        */
/*! \file shared_terms_database.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

#include "context/cdhashset.h"
#include "expr/node.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"
#include "util/statistics_registry.h"

namespace CVC4 {

class TheoryEngine;

class SharedTermsDatabase : public context::ContextNotifyObj {

public:

  /** A container for a list of shared terms */
  typedef std::vector<TNode> shared_terms_list;

  /** The iterator to go through the shared terms list */
  typedef shared_terms_list::const_iterator shared_terms_iterator;

private:

  /** Some statistics */
  IntStat d_statSharedTerms;

  // Needs to be a map from Nodes as after a backtrack they might not exist
  typedef std::hash_map<Node, shared_terms_list, TNodeHashFunction> SharedTermsMap;

  /** A map from atoms to a list of shared terms */
  SharedTermsMap d_atomsToTerms;

  /** Each time we add a shared term, we add it's parent to this list */
  std::vector<TNode> d_addedSharedTerms;

  /** Context-dependent size of the d_addedSharedTerms list */
  context::CDO<unsigned> d_addedSharedTermsSize;

  /** A map from atoms and subterms to the theories that use it */
  typedef context::CDHashMap<std::pair<Node, TNode>, theory::Theory::Set, TNodePairHashFunction> SharedTermsTheoriesMap;
  SharedTermsTheoriesMap d_termsToTheories;

  /** Map from term to theories that have already been notified about the shared term */
  typedef context::CDHashMap<TNode, theory::Theory::Set, TNodeHashFunction> AlreadyNotifiedMap;
  AlreadyNotifiedMap d_alreadyNotifiedMap;

  /** The registered equalities for propagation */
  typedef context::CDHashSet<Node, NodeHashFunction> RegisteredEqualitiesSet;
  RegisteredEqualitiesSet d_registeredEqualities;

private:

  /** This method removes all the un-necessary stuff from the maps */
  void backtrack();

  // EENotifyClass: template helper class for d_equalityEngine - handles call-backs
  class EENotifyClass : public theory::eq::EqualityEngineNotify {
    SharedTermsDatabase& d_sharedTerms;
  public:
    EENotifyClass(SharedTermsDatabase& shared): d_sharedTerms(shared) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value) {
      d_sharedTerms.propagateEquality(equality, value);
      return true;
    }

    bool eqNotifyTriggerPredicate(TNode predicate, bool value) {
      Unreachable();
      return true;
    }

    bool eqNotifyTriggerTermEquality(theory::TheoryId tag, TNode t1, TNode t2, bool value) {
      return d_sharedTerms.propagateSharedEquality(tag, t1, t2, value);
    }

    void eqNotifyConstantTermMerge(TNode t1, TNode t2) {
      d_sharedTerms.conflict(t1, t2, true);
    }

    void eqNotifyNewClass(TNode t) { }
    void eqNotifyPreMerge(TNode t1, TNode t2) { }
    void eqNotifyPostMerge(TNode t1, TNode t2) { }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) { }
  };

  /** The notify class for d_equalityEngine */
  EENotifyClass d_EENotify;

  /** Equality engine */
  theory::eq::EqualityEngine d_equalityEngine;

  /**
   * Method called by equalityEngine when a becomes (dis-)equal to b and a and b are shared with
   * the theory. Returns false if there is a direct conflict (via rewrite for example).
   */
  bool propagateSharedEquality(theory::TheoryId theory, TNode a, TNode b, bool value);

  /**
   * Called from the equality engine when a trigger equality is deduced.
   */
  bool propagateEquality(TNode equality, bool polarity);

  /** Theory engine */
  TheoryEngine* d_theoryEngine;

  /** Are we in conflict */
  context::CDO<bool> d_inConflict;

  /** Conflicting terms, if any */
  Node d_conflictLHS, d_conflictRHS;

  /** Polarity of the conflict */
  bool d_conflictPolarity;

  /** Called by the equality engine notify to mark the conflict */
  void conflict(TNode lhs, TNode rhs, bool polarity) {
    if (!d_inConflict) {
      // Only remember it if we're not already in conflict
      d_inConflict = true;
      d_conflictLHS = lhs;
      d_conflictRHS = rhs;
      d_conflictPolarity = polarity;
    }
  }

  /**
   * Should be called before any public non-const method in order to
   * enqueue the conflict to the theory engine.
   */
  void checkForConflict();

public:

  SharedTermsDatabase(TheoryEngine* theoryEngine, context::Context* context);
  ~SharedTermsDatabase();

  /**
   * Asserts the equality to the shared terms database,
   */
  void assertEquality(TNode equality, bool polarity, TNode reason);

  /**
   * Return whether the equality is alreday known to the engine
   */
  bool isKnown(TNode literal) const;

  /**
   * Returns an explanation of the propagation that came from the database.
   */
  Node explain(TNode literal) const;

  /**
   * Add an equality to propagate.
   */
  void addEqualityToPropagate(TNode equality);

  /**
   * Add a shared term to the database. The shared term is a subterm of the atom and
   * should be associated with the given theory.
   */
  void addSharedTerm(TNode atom, TNode term, theory::Theory::Set theories);

  /**
   * Mark that the given theories have been notified of the given shared term.
   */
  void markNotified(TNode term, theory::Theory::Set theories);

  /**
   * Returns true if the atom contains any shared terms, false otherwise.
   */
  bool hasSharedTerms(TNode atom) const;

  /**
   * Iterator pointing to the first shared term belonging to the given atom.
   */
  shared_terms_iterator begin(TNode atom) const;

  /**
   * Iterator pointing to the end of the list of shared terms belonging to the given atom.
   */
  shared_terms_iterator end(TNode atom) const;

  /**
   * Get the theories that share the term in a given atom (and have not yet been notified).
   */
  theory::Theory::Set getTheoriesToNotify(TNode atom, TNode term) const;

  /**
   * Get the theories that share the term and have been notified already.
   */
  theory::Theory::Set getNotifiedTheories(TNode term) const;

  /**
   * Returns true if the term is currently registered as shared with some theory.
   */
  bool isShared(TNode term) const {
    return d_alreadyNotifiedMap.find(term) != d_alreadyNotifiedMap.end();
  }

  /**
   * Returns true if the literal is an (dis-)equality with both sides registered as shared with
   * some theory.
   */
  bool isSharedEquality(TNode literal) const {
    TNode atom = literal.getKind() == kind::NOT ? literal[0] : literal;
    return atom.getKind() == kind::EQUAL && isShared(atom[0]) && isShared(atom[1]);
  }

  /**
   * Returns true if the shared terms a and b are known to be equal.
   */
  bool areEqual(TNode a, TNode b) const;

  /**
   * Retursn true if the shared terms a and b are known to be dis-equal.
   */
  bool areDisequal(TNode a, TNode b) const;

  /**
   * get equality engine
   */
  theory::eq::EqualityEngine* getEqualityEngine() { return &d_equalityEngine; }

protected:

  /**
   * This method gets called on backtracks from the context manager.
   */
  void contextNotifyPop() {
    backtrack();
  }
};

}
