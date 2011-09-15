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

namespace CVC4 {

class SharedTermsDatabase : public context::ContextNotifyObj {

public:

  /** A conainer for a list of shared terms */
  typedef std::vector<TNode> shared_terms_list;
  /** The iterator to go rhough the shared terms list */
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
  
  typedef context::CDMap<std::pair<Node, TNode>, theory::Theory::Set, TNodePairHashFunction> SharedTermsTheoriesMap;
  /** A map from atoms and subterms to the theories that use it */
  SharedTermsTheoriesMap d_termsToTheories;

  typedef context::CDMap<TNode, theory::Theory::Set, TNodeHashFunction> AlreadyNotifiedMap;
  /** Map from term to theories that have already been notified about the shared term */
  AlreadyNotifiedMap d_alreadyNotifiedMap;

  /** This method removes all the un-necessary stuff from the maps */
  void backtrack();

public:

  SharedTermsDatabase(context::Context* context)
  : ContextNotifyObj(context),
    d_context(context), 
    d_statSharedTerms("theory::shared_terms", 0),
    d_addedSharedTermsSize(context, 0),
    d_termsToTheories(context),
    d_alreadyNotifiedMap(context) 
  {
    StatisticsRegistry::registerStat(&d_statSharedTerms);
  }

  ~SharedTermsDatabase() throw(AssertionException)
  {
    StatisticsRegistry::unregisterStat(&d_statSharedTerms);
  }
  
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
   
  /**
   * This method gets called on backtracks from the context manager.
   */
  void notify() {
    backtrack();
  }
};

}

