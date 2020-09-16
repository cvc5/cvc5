/*********************                                                        */
/*! \file sort_inference.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Paul Meng, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Pre-process step for performing sort inference
 **/

#include "cvc4_private.h"

#ifndef CVC4__SORT_INFERENCE_H
#define CVC4__SORT_INFERENCE_H

#include <iostream>
#include <string>
#include <vector>
#include <map>
#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {

/** sort inference
 *
 * This class implements sort inference techniques, which rewrites a
 * formula F into an equisatisfiable formula F', where the symbols g in F are
 * replaced by others g', possibly of different types. For details, see e.g.:
 *   "Sort it out with Monotonicity" Claessen 2011
 *   "Non-Cyclic Sorts for First-Order Satisfiability" Korovin 2013.
 */
class SortInference {
private:
  //all subsorts
  std::vector< int > d_sub_sorts;
  std::map< int, bool > d_non_monotonic_sorts;
  std::map< TypeNode, std::vector< int > > d_type_sub_sorts;
  void recordSubsort( TypeNode tn, int s );
public:
  class UnionFind {
  public:
    UnionFind(){}
    UnionFind( UnionFind& c ){
      set( c );
    }
    std::map< int, int > d_eqc;
    //pairs that must be disequal
    std::vector< std::pair< int, int > > d_deq;
    void print(const char * c);
    void clear() { d_eqc.clear(); d_deq.clear(); }
    void set( UnionFind& c );
    int getRepresentative( int t );
    void setEqual( int t1, int t2 );
    void setDisequal( int t1, int t2 ){ d_deq.push_back( std::pair< int, int >( t1, t2 ) ); }
    bool areEqual( int t1, int t2 ) { return getRepresentative( t1 )==getRepresentative( t2 ); }
    bool isValid();
  };

 private:
  /** the id count for all subsorts we have allocated */
  int d_sortCount;
  UnionFind d_type_union_find;
  std::map< int, TypeNode > d_type_types;
  std::map< TypeNode, int > d_id_for_types;
  //for apply uf operators
  std::map< Node, int > d_op_return_types;
  std::map< Node, std::vector< int > > d_op_arg_types;
  std::map< Node, int > d_equality_types;
  //for bound variables
  std::map< Node, std::map< Node, int > > d_var_types;
  //get representative
  void setEqual( int t1, int t2 );
  int getIdForType( TypeNode tn );
  void printSort( const char* c, int t );
  //process
  int process( Node n, std::map< Node, Node >& var_bound, std::map< Node, int >& visited );
  // for monotonicity inference
 private:
  void processMonotonic( Node n, bool pol, bool hasPol, std::map< Node, Node >& var_bound, std::map< Node, std::map< int, bool > >& visited, bool typeMode = false );

//for rewriting
private:
  //mapping from old symbols to new symbols
  std::map< Node, Node > d_symbol_map;
  //mapping from constants to new symbols
  std::map< TypeNode, std::map< Node, Node > > d_const_map;
  //helper functions for simplify
  TypeNode getOrCreateTypeForId( int t, TypeNode pref );
  TypeNode getTypeForId( int t );
  Node getNewSymbol( Node old, TypeNode tn );
  //simplify
  Node simplifyNode(Node n,
                    std::map<Node, Node>& var_bound,
                    TypeNode tnn,
                    std::map<Node, Node>& model_replace_f,
                    std::map<Node, std::map<TypeNode, Node> >& visited);
  //make injection
  Node mkInjection( TypeNode tn1, TypeNode tn2 );
  //reset
  void reset();

 public:
  SortInference() : d_sortCount(1) {}
  ~SortInference(){}

  /** initialize
   *
   * This initializes this class. The input formula is indicated by assertions.
   */
  void initialize(const std::vector<Node>& assertions);
  /** simplify
   *
   * This returns the simplified form of formula n, based on the information
   * computed during initialization. The argument model_replace_f stores the
   * mapping between functions and their analog in the sort-inferred signature.
   * The argument visited is a cache of the internal results of simplifying
   * previous nodes with this class.
   *
   * Must call initialize() before this function.
   */
  Node simplify(Node n,
                std::map<Node, Node>& model_replace_f,
                std::map<Node, std::map<TypeNode, Node> >& visited);
  /** get new constraints
   *
   * This adds constraints to new_asserts that ensure the following.
   * Let F be the conjunction of assertions from the input. Let F' be the
   * conjunction of the simplified form of each conjunct in F. Let C be the
   * conjunction of formulas adding to new_asserts. Then, F and F' ^ C are
   * equisatisfiable.
   */
  void getNewAssertions(std::vector<Node>& new_asserts);
  /** compute monotonicity
   *
   * This computes whether sorts are monotonic (see e.g. Claessen 2011). If
   * this function is called, then calls to isMonotonic() can subsequently be
   * used to query whether sorts are monotonic.
   */
  void computeMonotonicity(const std::vector<Node>& assertions);
  /** return true if tn was inferred to be monotonic */
  bool isMonotonic(TypeNode tn);
  //get sort id for term n
  int getSortId( Node n );
  //get sort id for variable of quantified formula f
  int getSortId( Node f, Node v );
  //set that sk is the skolem variable of v for quantifier f
  void setSkolemVar( Node f, Node v, Node sk );
public:
  //is well sorted
  bool isWellSortedFormula( Node n );
  bool isWellSorted( Node n );
private:
  // store monotonicity for original sorts as well
 std::map<TypeNode, bool> d_non_monotonic_sorts_orig;
 /**
  * Returns true if k is the APPLY_UF kind and we are not using higher-order
  * techniques. This is called in places where we want to know whether to
  * treat a term as uninterpreted function.
  */
 bool isHandledApplyUf(Kind k) const;
};

}

#endif
