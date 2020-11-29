/*********************                                                        */
/*! \file term_registration_visitor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

#include "context/context.h"
#include "theory/shared_terms_database.h"

#include <unordered_map>

namespace CVC4 {

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
class PreRegisterVisitor {

  /** The engine */
  TheoryEngine* d_engine;

  typedef context::CDHashMap<TNode, theory::TheoryIdSet, TNodeHashFunction>
      TNodeToTheorySetMap;

  /**
   * Map from terms to the theories that have already had this term pre-registered.
   */
  TNodeToTheorySetMap d_visited;

  /**
   * A set of all theories in the term
   */
  theory::TheoryIdSet d_theories;

  /**
   * String representation of the visited map, for debugging purposes.
   */
  std::string toString() const;

 public:
  /** Returned set tells us which theories there are */
  typedef theory::TheoryIdSet return_type;

  PreRegisterVisitor(TheoryEngine* engine, context::Context* context)
      : d_engine(engine), d_visited(context), d_theories(0)
  {
  }

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
   * Marks the node as the starting literal.
   */
  void start(TNode node) {}

  /**
   * Notifies the engine of all the theories used.
   */
  theory::TheoryIdSet done(TNode node) { return d_theories; }
};


/**
 * The reason why we need to make this outside of the pre-registration loop is because we need a shared term x to 
 * be associated with every atom that contains it. For example, if given f(x) >= 0 and f(x) + 1 >= 0, although f(x) has
 * been visited already, we need to visit it again, since we need to associate it with both atoms.
 */
class SharedTermsVisitor {

  /** The shared terms database */
  SharedTermsDatabase& d_sharedTerms;

  /**
   * Cache from preprocessing of atoms.
   */
  typedef std::unordered_map<TNode, theory::TheoryIdSet, TNodeHashFunction>
      TNodeVisitedMap;
  TNodeVisitedMap d_visited;

  /**
   * String representation of the visited map, for debugging purposes.
   */
  std::string toString() const;

  /** 
   * The initial atom.
   */
  TNode d_atom; 
    
public:

  typedef void return_type;

  SharedTermsVisitor(SharedTermsDatabase& sharedTerms)
  : d_sharedTerms(sharedTerms) {}

  /**
   * Returns true is current has already been pre-registered with both current and parent theories.
   */
  bool alreadyVisited(TNode current, TNode parent) const;
  
  /**
   * Pre-registeres current with any of the current and parent theories that haven't seen the term yet.
   */
  void visit(TNode current, TNode parent);
  
  /**
   * Marks the node as the starting literal.
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
};


}
