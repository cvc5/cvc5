/*********************                                                        */
/*! \file theory_datatypes.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of datatypes.
 **
 ** Theory of datatypes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H
#define __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H

#include "theory/theory.h"
#include "util/congruence_closure.h"
#include "util/datatype.h"
#include "theory/datatypes/union_find.h"
#include "util/hash.h"
#include "util/trans_closure.h"
#include "theory/datatypes/explanation_manager.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

namespace CVC4 {
namespace theory {
namespace datatypes {

class TheoryDatatypes : public Theory {
private:
  typedef context::CDChunkList<TNode> EqList;
  typedef context::CDHashMap<Node, EqList*, NodeHashFunction> EqLists;
  typedef context::CDChunkList<Node> EqListN;
  typedef context::CDHashMap<Node, EqListN*, NodeHashFunction> EqListsN;
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;

  /** for debugging */
  context::CDList<Node> d_currAsserts;
  context::CDList<Node> d_currEqualities;

  /** keeps track of all selectors we care about, value is whether they have been collapsed */
  BoolMap d_selectors;
  /** keeps track of which nodes are representatives */
  BoolMap d_reps;
  /** map from (representative) nodes to a list of selectors whose arguments are 
      in the equivalence class of that node */
  EqListsN d_selector_eq;
  /** map from (representative) nodes to list of nodes in their eq class */
  EqListsN d_equivalence_class;
  /** map from nodes to whether they have been instantiated */
  BoolMap d_inst_map;
  /** transitive closure to record equivalence/subterm relation.  */
  TransitiveClosureNode d_cycle_check;
  /** has seen cycle */
  context::CDO< bool > d_hasSeenCycle;
  /** get the constructor for the node */
  const DatatypeConstructor& getConstructor( Node cons );
  /** get the constructor for the selector */
  Node getConstructorForSelector( Node sel );

  /**
   * map from (representative) nodes to testers that hold for that node
   * for each t, this is either a list of equations of the form
   *   NOT is_[constructor_1]( t )...NOT is_[constructor_n]( t ), each of which are unique testers
   *   and n is less than the number of possible constructors for t minus one,
   * or a list of equations of the form
   *   NOT is_[constructor_1]( t )...NOT is_[constructor_n]( t )  followed by
   *   is_[constructor_(n+1)]( t ), each of which is a unique tester.
   */
  EqLists d_labels;

  class CongruenceChannel {
    TheoryDatatypes* d_datatypes;

  public:
    CongruenceChannel(TheoryDatatypes* datatypes) : d_datatypes(datatypes) {}
    void notifyCongruent(TNode a, TNode b) {
      d_datatypes->notifyCongruent(a, b);
    }
  };/* class CongruenceChannel */
  friend class CongruenceChannel;

  /**
   * Output channel connected to the congruence closure module.
   */
  CongruenceChannel d_ccChannel;

  /**
   * Instance of the congruence closure module.
   */
  CongruenceClosure<CongruenceChannel, CONGRUENCE_OPERATORS_2 (kind::APPLY_CONSTRUCTOR, kind::APPLY_SELECTOR)> d_cc;

  /**
   * Union find for storing the equalities.
   */
  UnionFind<Node, NodeHashFunction> d_unionFind;

  /**
   * Received a notification from the congruence closure algorithm that the two nodes
   * a and b have been merged.
   */
  void notifyCongruent(TNode a, TNode b);

  /**
   * List of all disequalities this theory has seen.
   * Maintaints the invariant that if a is in the
   * disequality list of b, then b is in that of a.
   * */
  EqLists d_disequalities;

  /**
   * information for delayed merging (is this necessary?)
   */
  std::vector< std::vector< std::pair< Node, Node > > > d_merge_pending;

  /**
   * Terms that currently need to be checked for collapse/instantiation rules
   */
  std::map< Node, bool > d_checkMap;

  /**
   * explanation manager
   */
  ExplanationManager d_em;

  /**
   * explanation manager for the congruence closure module
   */
  CongruenceClosureExplainer<CongruenceChannel, CONGRUENCE_OPERATORS_2 (kind::APPLY_CONSTRUCTOR, kind::APPLY_SELECTOR)> d_cce;

public:
  TheoryDatatypes(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation);
  ~TheoryDatatypes();
  void preRegisterTerm(TNode n);
  void presolve();

  void addSharedTerm(TNode t);
  void notifyEq(TNode lhs, TNode rhs);
  void check(Effort e);
  Node getValue(TNode n);
  void shutdown() { }
  std::string identify() const { return std::string("TheoryDatatypes"); }

private:
  /* Helper methods */
  bool checkTester( Node assertion, Node& conflict, unsigned& r );
  void addTester( Node assertion );
  Node getInstantiateCons( Node t );
  void checkInstantiateEqClass( Node t );
  bool checkInstantiate( Node te, Node cons );
  bool collapseSelector( Node t );
  void updateSelectors( Node a );
  void addTermToLabels( Node t );
  void initializeEqClass( Node t );
  void collectTerms( Node n, bool recurse = true );
  bool hasConflict();

  /* from uf_morgan */
  void merge(TNode a, TNode b);
  inline TNode find(TNode a); 
  inline TNode debugFind(TNode a) const;
  void appendToDiseqList(TNode of, TNode eq);
  void addDisequality(TNode eq);
  void addEquality(TNode eq);

  void checkCycles();
  bool searchForCycle( Node n, Node on,
                       std::map< Node, bool >& visited,
                       NodeBuilder<>& explanation );
};/* class TheoryDatatypes */

inline bool TheoryDatatypes::hasConflict() { 
  return d_em.hasConflict(); 
}

inline TNode TheoryDatatypes::find(TNode a) {
  return d_unionFind.find(a);
}

inline TNode TheoryDatatypes::debugFind(TNode a) const {
  return d_unionFind.debugFind(a);
}


}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H */
