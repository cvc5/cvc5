/*********************                                                        */
/*! \file theory_datatypes.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
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

#include <ext/hash_set>
#include <iostream>
#include <map>

namespace CVC4 {
namespace theory {
namespace datatypes {

class TheoryDatatypes : public Theory {
private:
  typedef context::CDList<TNode, context::ContextMemoryAllocator<TNode> > EqList;
  typedef context::CDMap<Node, EqList*, NodeHashFunction> EqLists;
  typedef context::CDList<Node, context::ContextMemoryAllocator<Node> > EqListN;
  typedef context::CDMap<Node, EqListN*, NodeHashFunction> EqListsN;
  typedef context::CDMap< Node, bool, NodeHashFunction > BoolMap;

  std::hash_set<TypeNode, TypeNodeHashFunction> d_addedDatatypes;

  context::CDList<Node> d_currAsserts;
  context::CDList<Node> d_currEqualities;
  /** a list of types with the list of constructors for that type */
  std::map<TypeNode, std::vector<Node> > d_cons;
  /** a list of types with the list of constructors for that type */
  std::map<TypeNode, std::vector<Node> > d_testers;
  /** a list of constructors with the list of selectors */
  std::map<Node, std::vector<Node> > d_sels;
  /** map from selectors to the constructors they are for */
  std::map<Node, Node > d_sel_cons;
  /**  the distinguished ground term for each type */
  std::map<TypeNode, Node > d_distinguishTerms;
  /** finite datatypes/constructor */
  std::map< TypeNode, bool > d_finite;
  std::map< Node, bool > d_cons_finite;
  /** well founded datatypes/constructor */
  std::map< TypeNode, bool > d_wellFounded;
  std::map< Node, bool > d_cons_wellFounded;
  /** whether we need to check finite and well foundedness */
  bool requiresCheckFiniteWellFounded;
  /** map from equalties and the equalities they are derived from */
  context::CDMap< Node, Node, NodeHashFunction > d_drv_map;
  /** equalities that are axioms */
  BoolMap d_axioms;
  /** list of all selectors */
  BoolMap d_selectors;
  /** list of all representatives */
  BoolMap d_reps;
  /** map from nodes to a list of selectors whose arguments are in the equivalence class of that node */
  EqListsN d_selector_eq;
  /** map from node representatives to list of nodes in their eq class */
  EqListsN d_equivalence_class;
  /** map from terms to whether they have been instantiated */
  BoolMap d_inst_map;
  //Type getType( TypeNode t );
  int getConstructorIndex( TypeNode t, Node c );
  int getTesterIndex( TypeNode t, Node c );
  bool isDatatype( TypeNode t ) { return d_cons.find( t )!=d_cons.end(); }
  void checkFiniteWellFounded();

  /**
   * map from terms to testers asserted for that term
   * for each t, this is either a list of equations of the form
   *   NOT is_[constructor_1]( t )...NOT is_[constructor_n]( t ), each of which are unique testers,
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

  /** List of all (potential) equalities to be propagated. */
  EqLists d_equalities;

  /**
   * stores the conflicting disequality (still need to call construct
   * conflict to get the actual explanation)
   */
  Node d_conflict;
  bool d_noMerge;
  std::vector< std::vector< std::pair< Node, Node > > > d_merge_pending;
public:
  TheoryDatatypes(context::Context* c, OutputChannel& out, Valuation valuation);
  ~TheoryDatatypes();
  void preRegisterTerm(TNode n) {
    TypeNode type = n.getType();
    if(type.getKind() == kind::DATATYPE_TYPE) {
      addDatatypeDefinitions(type);
    }
  }
  void registerTerm(TNode n) { }

  void presolve();

  void addSharedTerm(TNode t);
  void notifyEq(TNode lhs, TNode rhs);
  void check(Effort e);
  void propagate(Effort e) { }
  void explain(TNode n, Effort e) { }
  Node getValue(TNode n);
  void shutdown() { }
  std::string identify() const { return std::string("TheoryDatatypes"); }

  void addDatatypeDefinitions(TypeNode dttn);

private:
  /* Helper methods */
  void checkTester( Node assertion, bool doAdd = true );
  static bool checkTrivialTester(Node assertion);
  void checkInstantiate( Node t );
  Node getPossibleCons( Node t, bool checkInst = false );
  Node collapseSelector( TNode t, bool useContext = false );
  void updateSelectors( Node a );
  void collectTerms( TNode t );
  void addTermToLabels( Node t );
  void initializeEqClass( Node t );

  /* from uf_morgan */
  void merge(TNode a, TNode b);
  inline TNode find(TNode a);
  inline TNode debugFind(TNode a) const;
  void appendToDiseqList(TNode of, TNode eq);
  void appendToEqList(TNode of, TNode eq);
  void addDisequality(TNode eq);
  void addDerivedEquality(TNode eq, TNode jeq);
  void addEquality(TNode eq);
  void registerEqualityForPropagation(TNode eq);
  void convertDerived(Node n, NodeBuilder<>& nb);
  void throwConflict();

  void checkCycles();
  bool searchForCycle( Node n, Node on,
                       std::map< Node, bool >& visited,
                       NodeBuilder<>& explanation );
  bool checkClash( Node n1, Node n2, NodeBuilder<>& explanation );
  static bool checkClashSimple( Node n1, Node n2 );
  friend class DatatypesRewriter;// for access to checkClashSimple();
};/* class TheoryDatatypes */

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
