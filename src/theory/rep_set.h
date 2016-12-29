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
  /** debug print */
  void toStream(std::ostream& out);
};/* class RepSet */

//representative domain
typedef std::vector< int > RepDomain;


class RepBoundExt {
 public:
  virtual ~RepBoundExt() {}
  virtual bool setBound( Node owner, int i, TypeNode tn, std::vector< Node >& elements ) = 0;
};

/** this class iterates over a RepSet */
class RepSetIterator {
public:
  enum {
    ENUM_DEFAULT,
    ENUM_BOUND_INT,
  };
private:
  QuantifiersEngine * d_qe;
  //initialize function
  bool initialize( RepBoundExt* rext = NULL );
  //for int ranges
  std::map< int, Node > d_lower_bounds;
  //for set ranges
  std::map< int, std::vector< Node > > d_setm_bounds;
  //domain size
  int domainSize( int i );
  //node this is rep set iterator is for
  Node d_owner;
  //reset index, 1:success, 0:empty, -1:fail
  int resetIndex( int i, bool initial = false );
  /** set index order */
  void setIndexOrder( std::vector< int >& indexOrder );
  /** do reset increment the iterator at index=counter */
  int do_reset_increment( int counter, bool initial = false );
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
  //are we only considering a strict subset of the domain of the quantifier?
  bool d_incomplete;
public:
  RepSetIterator( QuantifiersEngine * qe, RepSet* rs );
  ~RepSetIterator(){}
  //set that this iterator will be iterating over instantiations for a quantifier
  bool setQuantifier( Node f, RepBoundExt* rext = NULL );
  //set that this iterator will be iterating over the domain of a function
  bool setFunctionDomain( Node op, RepBoundExt* rext = NULL );
public:
  //pointer to model
  RepSet* d_rep_set;
  //enumeration type?
  std::vector< int > d_enum_type;
  //current tuple we are considering
  std::vector< int > d_index;
  //types we are considering
  std::vector< TypeNode > d_types;
  //domain we are considering
  std::vector< std::vector< Node > > d_domain_elements;
public:
  /** increment the iterator at index=counter */
  int increment2( int i );
  /** increment the iterator */
  int increment();
  /** is the iterator finished? */
  bool isFinished();
  /** get the i_th term we are considering */
  Node getCurrentTerm( int v );
  /** get the number of terms we are considering */
  int getNumTerms() { return (int)d_index_order.size(); }
  /** debug print */
  void debugPrint( const char* c );
  void debugPrintSmall( const char* c );
  //get index order, returns var #
  int getIndexOrder( int v ) { return d_index_order[v]; }
  //get variable order, returns index #
  int getVariableOrder( int i ) { return d_var_order[i]; }
  //is incomplete
  bool isIncomplete() { return d_incomplete; }
};/* class RepSetIterator */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__REP_SET_H */
