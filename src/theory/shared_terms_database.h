/*********************                                                        */
/*! \file node_visitor.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: 
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **/

#pragma once

#include "cvc4_private.h"

#include "expr/node.h"
#include "theory/theory.h"
#include "context/context.h"
#include "util/stats.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {

class SharedTermsDatabase : public context::ContextNotifyObj {

public:

  /** A container for a list of shared terms */
  typedef std::vector<TNode> shared_terms_list;

  /** The iterator to go through the shared terms list */
  typedef shared_terms_list::const_iterator shared_terms_iterator;

private:

  /** The context */
  context::Context* d_context;
  
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
  
  typedef context::CDHashMap<std::pair<Node, TNode>, theory::Theory::Set, TNodePairHashFunction> SharedTermsTheoriesMap;

  /** A map from atoms and subterms to the theories that use it */
  SharedTermsTheoriesMap d_termsToTheories;

  typedef context::CDHashMap<TNode, theory::Theory::Set, TNodeHashFunction> AlreadyNotifiedMap;

  /** Map from term to theories that have already been notified about the shared term */
  AlreadyNotifiedMap d_alreadyNotifiedMap;

public:

  /** Class for notifications about new shared term equalities */
  class SharedTermsNotifyClass {
    public:
      SharedTermsNotifyClass() {}
      virtual ~SharedTermsNotifyClass() {}
      virtual void notify(TNode literal, TNode original, theory::TheoryId theory) = 0;
  };

private:

  // Instance of class to send shared term notifications to
  SharedTermsNotifyClass& d_sharedNotify;

  // Type for list of theory, node pairs: theory is theory to be notified,
  // node is the representative for this equivalence class known to the
  // theory that will be notified
  typedef context::CDHashMap<theory::TheoryId, TNode, __gnu_cxx::hash<unsigned> > NotifyList;
  typedef context::CDHashMap<TNode, NotifyList*, TNodeHashFunction> TermToNotifyList;

  // Map from terms (only valid for reps) to their notify lists
  // Note that theory, term pairs only need to be in the notify list if the
  // representative term is not a valid shared term for the theory.
  TermToNotifyList d_termToNotifyList;

  // List of allocated NotifyList* objects
  std::vector<NotifyList*> d_allocatedNL;

  // Total number of allocated NotifyList* objects
  unsigned d_allocatedNLSize;

  // Size of portion of d_allocatedNL that is currently in use
  context::CDO<unsigned> d_allocatedNLNext;

  /** This method removes all the un-necessary stuff from the maps */
  void backtrack();

  // EENotifyClass: template helper class for d_equalityEngine - handles call-backs
  class EENotifyClass : public theory::eq::EqualityEngineNotify {
    SharedTermsDatabase& d_sharedTerms;
  public:
    EENotifyClass(SharedTermsDatabase& shared): d_sharedTerms(shared) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value) {
      Unreachable();
      return true;
    }

    bool eqNotifyTriggerPredicate(TNode predicate, bool value) {
      Unreachable();
      return true;
    }

    bool eqNotifyTriggerTermEquality(TNode t1, TNode t2, bool value) {
      if (value) {
        d_sharedTerms.mergeSharedTerms(t1, t2);
      }
      return true;
    }

    bool eqNotifyConstantTermMerge(TNode t1, TNode t2) {
      return true;
    }
  };

  /** The notify class for d_equalityEngine */
  EENotifyClass d_EENotify;

  /** Equality engine */
  theory::eq::EqualityEngine d_equalityEngine;

  /** Attach a new notify list to an equivalence class representative */
  NotifyList* getNewNotifyList();

  /** Method called by equalityEngine when a becomes equal to b */
  void mergeSharedTerms(TNode a, TNode b);

public:

  SharedTermsDatabase(SharedTermsNotifyClass& notify, context::Context* context);
  ~SharedTermsDatabase() throw(AssertionException);
  
  /**
   * Add a shared term to the database. The shared term is a subterm of the atom and 
   * should be associated with the given theory. 
   */
  void addSharedTerm(TNode atom, TNode term, theory::Theory::Set theories);

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
   * Mark that the given theories have been notified of the given shared term.
   */
  void markNotified(TNode term, theory::Theory::Set theories);
   
  bool isShared(TNode term) const {
    return d_alreadyNotifiedMap.find(term) != d_alreadyNotifiedMap.end();
  }

  bool areEqual(TNode a, TNode b);

  bool areDisequal(TNode a, TNode b);

  void processSharedLiteral(TNode literal, TNode reason);

  Node explain(TNode literal);

protected:

  /**
   * This method gets called on backtracks from the context manager.
   */
  void contextNotifyPop() {
    backtrack();
  }
};

}

