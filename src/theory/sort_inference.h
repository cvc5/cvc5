/*********************                                                        */
/*! \file sort_inference.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Pre-process step for performing sort inference
 **/

#include "cvc4_private.h"

#ifndef __CVC4__SORT_INFERENCE_H
#define __CVC4__SORT_INFERENCE_H

#include <vector>
#include <map>
#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {

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
  int sortCount;
  int initialSortCount;
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
//for monotonicity inference
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
  Node simplifyNode( Node n, std::map< Node, Node >& var_bound, TypeNode tnn, std::map< Node, std::map< TypeNode, Node > >& visited );
  //make injection
  Node mkInjection( TypeNode tn1, TypeNode tn2 );
  //reset
  void reset();
public:
  SortInference() : sortCount( 1 ){}
  ~SortInference(){}

  void simplify( std::vector< Node >& assertions, bool doSortInference, bool doMonotonicyInference );
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
  //get constraints for being well-typed according to computed sub-types
  void getSortConstraints( Node n, SortInference::UnionFind& uf );
public:
  //list of all functions and the uninterpreted symbols they were replaced with
  std::map< Node, Node > d_model_replace_f;

private:
  // store monotonicity for original sorts as well
  std::map< TypeNode, bool > d_non_monotonic_sorts_orig;  
public:
  //is monotonic
  bool isMonotonic( TypeNode tn );  
};

}

#endif
