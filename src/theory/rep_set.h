/*********************                                                        */
/*! \file rep_set.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representative set class and utilities
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__REP_SET_H
#define __CVC4__THEORY__REP_SET_H

#include "expr/node.h"
#include <map>

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

/** this class stores a representative set */
class RepSet {
public:
  RepSet(){}
  ~RepSet(){}
  std::map< TypeNode, std::vector< Node > > d_type_reps;
  std::map< TypeNode, bool > d_type_complete;
  std::map< Node, int > d_tmap;
  std::map< TypeNode, int > d_type_rlv_rep;
  // map from values to terms they were assigned for
  std::map< Node, Node > d_values_to_terms;
  /** clear the set */
  void clear();
  /** has type */
  bool hasType( TypeNode tn ) const { return d_type_reps.find( tn )!=d_type_reps.end(); }
  /** has rep */
  bool hasRep( TypeNode tn, Node n );
  /** get cardinality for type */
  int getNumRepresentatives( TypeNode tn ) const;
  /** add representative for type */
  void add( TypeNode tn, Node n );
  /** returns index in d_type_reps for node n */
  int getIndexFor( Node n ) const;
  /** complete all values */
  bool complete( TypeNode t );
  /** get number of relevant ground representatives for type */
  int getNumRelevantGroundReps( TypeNode t );
  /** debug print */
  void toStream(std::ostream& out);
};/* class RepSet */

//representative domain
typedef std::vector< int > RepDomain;

/** this class iterates over a RepSet */
class RepSetIterator {
public:
  enum {
    ENUM_DOMAIN_ELEMENTS,
    ENUM_RANGE,
  };
private:
  QuantifiersEngine * d_qe;
  //initialize function
  bool initialize();
  //for enum ranges
  std::map< int, Node > d_lower_bounds;
  //domain size
  int domainSize( int i );
  //node this is rep set iterator is for
  Node d_owner;
  //reset index
  bool resetIndex( int i, bool initial = false );
  /** set index order */
  void setIndexOrder( std::vector< int >& indexOrder );
public:
  RepSetIterator( QuantifiersEngine * qe, RepSet* rs );
  ~RepSetIterator(){}
  //set that this iterator will be iterating over instantiations for a quantifier
  bool setQuantifier( Node f );
  //set that this iterator will be iterating over the domain of a function
  bool setFunctionDomain( Node op );
public:
  //pointer to model
  RepSet* d_rep_set;
  //enumeration type?
  std::vector< int > d_enum_type;
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
  //intervals
  std::map< int, Node > d_bounds[2];
public:
  /** increment the iterator at index=counter */
  int increment2( int counter );
  /** increment the iterator */
  int increment();
  /** is the iterator finished? */
  bool isFinished();
  /** get the i_th term we are considering */
  Node getTerm( int i );
  /** get the number of terms we are considering */
  int getNumTerms() { return (int)d_index_order.size(); }
  /** debug print */
  void debugPrint( const char* c );
  void debugPrintSmall( const char* c );
};/* class RepSetIterator */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__REP_SET_H */
