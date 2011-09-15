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

#include "context/context.h"
#include "theory/shared_terms_database.h"

#include <ext/hash_map>

namespace CVC4 {

class TheoryEngine;

/**
 * Visitor that calls the apropriate theory to preregister the term.
 */
class PreRegisterVisitor {

  /** The engine */
  TheoryEngine* d_engine;

  /**
   * Map from nodes to the theories that have already seen them.
   */
  typedef context::CDMap<TNode, theory::Theory::Set, TNodeHashFunction> TNodeVisitedMap;
  TNodeVisitedMap d_visited;

  /**
   * All the theories of the visitation.
   */
  theory::Theory::Set d_theories;

  /**
   * String representation of the visited map, for debugging purposes.
   */
  std::string toString() const;

  /**
   * Is there more than one theory involved.
   */
  bool d_multipleTheories;

public:

  /** Return type tells us if there are more than one theory or not */
  typedef bool return_type;
  
  PreRegisterVisitor(TheoryEngine* engine, context::Context* context)
  : d_engine(engine), d_visited(context), d_theories(0) {}

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
   * Notifies the engine of all the theories used.
   */
  bool done(TNode node);

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
   * Cache from proprocessing of atoms.
   */
  typedef std::hash_map<TNode, theory::Theory::Set, TNodeHashFunction> TNodeVisitedMap;
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
