/*********************                                                        */
/*! \file sort_inference.h
 ** \verbatim
 ** Original author: Andrew Reynolds <andrew.j.reynolds@gmail.com>
 ** Major contributors: Morgan Deters <mdeters@cs.nyu.edu>
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Pre-process step for performing sort inference
 **/

#include "cvc4_private.h"

#ifndef __CVC4__SORT_INFERENCE_H
#define __CVC4__SORT_INFERENCE_H

#include <iostream>
#include <string>
#include <vector>
#include <map>
#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {

class SortInference{
private:
  //for debugging
  //std::map< int, std::vector< Node > > d_type_eq_class;
private:
  int sortCount;
  std::map< int, int > d_type_union_find;
  std::map< int, TypeNode > d_type_types;
  std::map< TypeNode, int > d_id_for_types;
  //for apply uf operators
  std::map< Node, int > d_op_return_types;
  std::map< Node, std::vector< int > > d_op_arg_types;
  //for bound variables
  std::map< Node, std::map< Node, int > > d_var_types;
  //get representative
  int getRepresentative( int t );
  void setEqual( int t1, int t2 );
  int getIdForType( TypeNode tn );
  void printSort( const char* c, int t );
  //process
  int process( Node n, std::map< Node, Node >& var_bound );
private:
  //mapping from old symbols to new symbols
  std::map< Node, Node > d_symbol_map;
  //mapping from constants to new symbols
  std::map< TypeNode, std::map< Node, Node > > d_const_map;
  //number of subtypes generated
  std::map< TypeNode, int > d_subtype_count;
  //helper functions for simplify
  TypeNode getOrCreateTypeForId( int t, TypeNode pref );
  TypeNode getTypeForId( int t );
  Node getNewSymbol( Node old, TypeNode tn );
  //simplify
  Node simplify( Node n, std::map< Node, Node >& var_bound );
public:
  SortInference() : sortCount( 0 ){}
  ~SortInference(){}

  void simplify( std::vector< Node >& assertions, bool doRewrite = false );
  int getSortId( Node n );
  int getSortId( Node f, Node v );
  //set that sk is the skolem variable of v for quantifier f
  void setSkolemVar( Node f, Node v, Node sk );
};

}

#endif
