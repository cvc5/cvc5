/*********************                                                        */
/*! \file rep_set.h
 ** \verbatim
 ** Original author: Andrew Reynolds <andrew.j.reynolds@gmail.com>
 ** Major contributors: Morgan Deters <mdeters@cs.nyu.edu>
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Representative set class and utilities
 **/

#include "cvc4_private.h"

#ifndef __CVC4__REP_SET_H
#define __CVC4__REP_SET_H

#include "expr/node.h"
#include <map>

namespace CVC4 {
namespace theory {

/** this class stores a representative set */
class RepSet {
public:
  RepSet(){}
  ~RepSet(){}
  std::map< TypeNode, std::vector< Node > > d_type_reps;
  std::map< TypeNode, bool > d_type_complete;
  std::map< Node, int > d_tmap;
  /** clear the set */
  void clear();
  /** has type */
  bool hasType( TypeNode tn ) const { return d_type_reps.find( tn )!=d_type_reps.end(); }
  /** get cardinality for type */
  int getNumRepresentatives( TypeNode tn ) const;
  /** add representative for type */
  void add( Node n );
  /** returns index in d_type_reps for node n */
  int getIndexFor( Node n ) const;
  /** complete all values */
  void complete( TypeNode t );
  /** debug print */
  void toStream(std::ostream& out);
};

//representative domain
typedef std::vector< int > RepDomain;

/** this class iterates over a RepSet */
class RepSetIterator {
private:
  //initialize function
  bool initialize();
public:
  RepSetIterator( RepSet* rs );
  ~RepSetIterator(){}
  //set that this iterator will be iterating over instantiations for a quantifier
  bool setQuantifier( Node f );
  //set that this iterator will be iterating over the domain of a function
  bool setFunctionDomain( Node op );
public:
  //pointer to model
  RepSet* d_rep_set;
  //index we are considering
  std::vector< int > d_index;
  //types we are considering
  std::vector< TypeNode > d_types;
  //domain we are considering
  std::vector< RepDomain > d_domain;
  //are we only considering a strict subset of the domain of the quantifier?
  bool d_incomplete;
  //ordering for variables we are indexing over
  //  for example, given reps = { a, b } and quantifier forall( x, y, z ) P( x, y, z ) with d_index_order = { 2, 0, 1 },
  //    then we consider instantiations in this order:
  //      a/x a/y a/z
  //      a/x b/y a/z
  //      b/x a/y a/z
  //      b/x b/y a/z
  //      ...
  std::vector< int > d_index_order;
  //variables to index they are considered at
  //  for example, if d_index_order = { 2, 0, 1 }
  //    then d_var_order = { 0 -> 1, 1 -> 2, 2 -> 0 }
  std::map< int, int > d_var_order;
public:
  /** set index order */
  void setIndexOrder( std::vector< int >& indexOrder );
  /** set domain */
  void setDomain( std::vector< RepDomain >& domain );
  /** increment the iterator at index=counter */
  void increment2( int counter );
  /** increment the iterator */
  void increment();
  /** is the iterator finished? */
  bool isFinished();
  /** get the i_th term we are considering */
  Node getTerm( int i );
  /** get the number of terms we are considering */
  int getNumTerms() { return (int)d_index_order.size(); }
  /** debug print */
  void debugPrint( const char* c );
  void debugPrintSmall( const char* c );
};

}
}

#endif