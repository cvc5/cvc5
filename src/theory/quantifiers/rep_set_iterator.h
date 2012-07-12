/*********************                                                        */
/*! \file rep_set_iterator.h
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
 ** \brief rep_set_iterator class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__REP_SET_ITERATOR_H
#define __CVC4__REP_SET_ITERATOR_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/first_order_model.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** this class iterates over a RepSet */
class RepSetIterator {
public:
  RepSetIterator( Node f, FirstOrderModel* model );
  ~RepSetIterator(){}
  //pointer to quantifier
  Node d_f;
  //pointer to model
  FirstOrderModel* d_model;
  //index we are considering
  std::vector< int > d_index;
  //domain we are considering
  std::vector< RepDomain > d_domain;
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
  //the instantiation constants of d_f
  std::vector< Node > d_ic;
  //the current terms we are considering
  std::vector< Node > d_terms;
public:
  /** set index order */
  void setIndexOrder( std::vector< int >& indexOrder );
  /** set domain */
  void setDomain( std::vector< RepDomain >& domain );
  /** increment the iterator */
  void increment2( int counter );
  void increment();
  /** is the iterator finished? */
  bool isFinished();
  /** produce the match that this iterator represents */
  void getMatch( QuantifiersEngine* qe, InstMatch& m );
  /** get the i_th term we are considering */
  Node getTerm( int i );
  /** get the number of terms we are considering */
  int getNumTerms() { return d_f[0].getNumChildren(); }
  /** debug print */
  void debugPrint( const char* c );
  void debugPrintSmall( const char* c );
};

class RepSetEvaluator
{
private:
  FirstOrderModel* d_model;
  RepSetIterator* d_riter;
private: //for Theory UF:
  //map from terms to the models used to calculate their value
  std::map< Node, bool > d_eval_uf_use_default;
  std::map< Node, uf::UfModelTreeOrdered > d_eval_uf_model;
  void makeEvalUfModel( Node n );
  //index ordering to use for each term
  std::map< Node, std::vector< int > > d_eval_term_index_order;
  int getMaxVariableNum( int n );
  void makeEvalUfIndexOrder( Node n );
private:
  //default evaluate term function
  Node evaluateTermDefault( Node n, int& depIndex, std::vector< int >& childDepIndex );
  //temporary storing which literals have failed
  void clearEvalFailed( int index );
  std::map< Node, bool > d_eval_failed;
  std::map< int, std::vector< Node > > d_eval_failed_lits;
public:
  RepSetEvaluator( FirstOrderModel* m, RepSetIterator* ri );
  virtual ~RepSetEvaluator(){}
  /** evaluate functions */
  int evaluate( Node n, int& depIndex );
  int evaluateEquality( Node n1, Node n2, int& depIndex );
  Node evaluateTerm( Node n, int& depIndex );
public:
  //statistics
  int d_eval_formulas;
  int d_eval_eqs;
  int d_eval_uf_terms;
};


}
}
}

#endif
