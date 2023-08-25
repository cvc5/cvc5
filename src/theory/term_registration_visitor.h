/******************************************************************************
 * Top contributors (to current version):
 *   Dejan Jovanovic, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_private.h"

#pragma once

#include <unordered_map>

#include "context/context.h"
#include "smt/env_obj.h"
#include "theory/shared_terms_database.h"

namespace cvc5::internal {

class TheoryEngine;

/**
 * Visitor that calls the appropriate theory to pre-register the term. The visitor also keeps track
 * of the sets of theories that are involved in the terms, so that it can say if there are multiple
 * theories involved.
 *
 * A sub-term has been visited if the theories of both the parent and the term itself have already
 * visited this term.
 *
 * Computation of the set of theories in the original term are computed in the alreadyVisited method
 * so as no to skip any theories.
 */
class PreRegisterVisitor : protected EnvObj
{
  /** The engine */
  TheoryEngine* d_engine;

  typedef context::CDHashMap<TNode, theory::TheoryIdSet> TNodeToTheorySetMap;

  /**
   * Map from terms to the theories that have already had this term pre-registered.
   */
  TNodeToTheorySetMap d_visited;

  /**
   * String representation of the visited map, for debugging purposes.
   */
  std::string toString() const;

 public:
  /** required to instantiate template for NodeVisitor */
  using return_type = void;

  PreRegisterVisitor(Env& env, TheoryEngine* engine);

  /**
   * Returns true is current has already been pre-registered with both current
   * and parent theories.
   */
  bool alreadyVisited(TNode current, TNode parent);

  /**
   * Pre-registeres current with any of the current and parent theories that
   * haven't seen the term yet.
   */
  void visit(TNode current, TNode parent);

  /**
   * Marks the node as the starting literal, which does nothing. This method
   * is required to instantiate template for NodeVisitor.
   */
  void start(TNode node);

  /** Called when the visitor is finished with a term, do nothing */
  void done(TNode node) {}

  /**
   * Preregister the term current occuring under term parent.  This calls
   * Theory::preRegisterTerm for the theories of current and parent, as well
   * as the theory of current's type, if it is finite.
   *
   * This method takes a set of theories visitedTheories that have already
   * preregistered current and updates this set with the theories that
   * preregister current during this call
   *
   * @param te Pointer to the theory engine containing the theories
   * @param visitedTheories The theories that have already preregistered current
   * @param current The term to preregister
   * @param parent The parent term of current
   * @param preregTheories The theories that have already preregistered current.
   * If there is no theory sharing, this coincides with visitedTheories.
   * Otherwise, visitedTheories may be a subset of preregTheories.
   */
  static void preRegister(Env& env,
                          TheoryEngine* te,
                          theory::TheoryIdSet& visitedTheories,
                          TNode current,
                          TNode parent,
                          theory::TheoryIdSet preregTheories);

 private:
  /**
   * Helper for above, called whether we wish to register a term with a theory
   * given by an identifier id.
   */
  static void preRegisterWithTheory(TheoryEngine* te,
                                    theory::TheoryIdSet& visitedTheories,
                                    theory::TheoryId id,
                                    TNode current,
                                    TNode parent,
                                    theory::TheoryIdSet preregTheories);
};

/**
 * The reason why we need to make this outside of the pre-registration loop is because we need a shared term x to 
 * be associated with every atom that contains it. For example, if given f(x) >= 0 and f(x) + 1 >= 0, although f(x) has
 * been visited already, we need to visit it again, since we need to associate it with both atoms.
 */
class SharedTermsVisitor : protected EnvObj
{
  using TNodeVisitedMap = std::unordered_map<TNode, theory::TheoryIdSet>;
  using TNodeToTheorySetMap = context::CDHashMap<TNode, theory::TheoryIdSet>;
  /**
   * String representation of the visited map, for debugging purposes.
   */
  std::string toString() const;

  /** 
   * The initial atom.
   */
  TNode d_atom;

 public:
  /** required to instantiate template for NodeVisitor */
  using return_type = void;

  SharedTermsVisitor(Env& env,
                     TheoryEngine* te,
                     SharedTermsDatabase& sharedTerms);

  /**
   * Returns true is current has already been pre-registered with both current and parent theories.
   */
  bool alreadyVisited(TNode current, TNode parent) const;
  
  /**
   * Pre-registeres current with any of the current and parent theories that haven't seen the term yet.
   */
  void visit(TNode current, TNode parent);

  /**
   * Marks the node as the starting literal, which clears the state.
   */
  void start(TNode node);

  /**
   * Just clears the state.
   */
  void done(TNode node);

  /**
   * Clears the internal state.
   */   
  void clear();

 private:
  /** The engine */
  TheoryEngine* d_engine;
  /** The shared terms database */
  SharedTermsDatabase& d_sharedTerms;
  /** Cache of nodes we have visited in this traversal */
  TNodeVisitedMap d_visited;
  /** (Global) cache of nodes we have preregistered in this SAT context */
  TNodeToTheorySetMap d_preregistered;
};

}  // namespace cvc5::internal
