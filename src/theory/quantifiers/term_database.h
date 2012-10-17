/*********************                                                        */
/*! \file term_database.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief term database class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H
#define __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H

#include "theory/theory.h"

#include <map>

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace inst{
  class Trigger;
}

namespace quantifiers {

class TermArgTrie {
private:
  bool addTerm2( QuantifiersEngine* qe, Node n, int argIndex );
public:
  /** the data */
  std::map< Node, TermArgTrie > d_data;
public:
  bool addTerm( QuantifiersEngine* qe, Node n ) { return addTerm2( qe, n, 0 ); }
};/* class TermArgTrie */


/** a trie of triggers */
class TrTrie {
private:
  inst::Trigger* getTrigger2( std::vector< Node >& nodes );
  void addTrigger2( std::vector< Node >& nodes, inst::Trigger* t );
public:
  TrTrie() : d_tr( NULL ){}
  inst::Trigger* d_tr;
  std::map< TNode, TrTrie* > d_children;
  inst::Trigger* getTrigger( std::vector< Node >& nodes ){
    std::vector< Node > temp;
    temp.insert( temp.begin(), nodes.begin(), nodes.end() );
    std::sort( temp.begin(), temp.end() );
    return getTrigger2( temp );
  }
  void addTrigger( std::vector< Node >& nodes, inst::Trigger* t ){
    std::vector< Node > temp;
    temp.insert( temp.begin(), nodes.begin(), nodes.end() );
    std::sort( temp.begin(), temp.end() );
    return addTrigger2( temp, t );
  }
};/* class inst::Trigger::TrTrie */


class TermDb {
  friend class ::CVC4::theory::QuantifiersEngine;
  friend class ::CVC4::theory::inst::Trigger;
private:
  /** reference to the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  /** calculated no match terms */
  bool d_matching_active;
  /** terms processed */
  std::hash_set< Node, NodeHashFunction > d_processed;
public:
  TermDb( QuantifiersEngine* qe ) : d_quantEngine( qe ), d_matching_active( true ){}
  ~TermDb(){}
  /** map from APPLY_UF operators to ground terms for that operator */
  std::map< Node, std::vector< Node > > d_op_map;
  /** map from APPLY_UF functions to trie */
  std::map< Node, TermArgTrie > d_func_map_trie;
  /** map from APPLY_UF predicates to trie */
  std::map< Node, TermArgTrie > d_pred_map_trie[2];
  /** map from type nodes to terms of that type */
  std::map< TypeNode, std::vector< Node > > d_type_map;
  /** add a term to the database */
  void addTerm( Node n, std::set< Node >& added, bool withinQuant = false );
  /** reset (calculate which terms are active) */
  void reset( Theory::Effort effort );
  /** set active */
  void setMatchingActive( bool a ) { d_matching_active = a; }
  /** get active */
  bool getMatchingActive() { return d_matching_active; }
private:
  /** for efficient e-matching */
  void addTermEfficient( Node n, std::set< Node >& added);
public:
  /** parent structure (for efficient E-matching):
      n -> op -> index -> L
      map from node "n" to a list of nodes "L", where each node n' in L
        has operator "op", and n'["index"] = n.
      for example, d_parents[n][f][1] = { f( t1, n ), f( t2, n ), ... }
  */
  /* Todo replace int by size_t */
  std::hash_map< Node, std::hash_map< Node, std::hash_map< int, std::vector< Node >  >, NodeHashFunction  > , NodeHashFunction > d_parents;
  const std::vector<Node> & getParents(TNode n, TNode f, int arg);

//for model basis
private:
  //map from types to model basis terms
  std::map< TypeNode, Node > d_model_basis_term;
  //map from ops to model basis terms
  std::map< Node, Node > d_model_basis_op_term;
  //map from instantiation terms to their model basis equivalent
  std::map< Node, Node > d_model_basis_body;
  /** map from universal quantifiers to model basis terms */
  std::map< Node, std::vector< Node > > d_model_basis_terms;
  // compute model basis arg
  void computeModelBasisArgAttribute( Node n );
public:
  //get model basis term
  Node getModelBasisTerm( TypeNode tn, int i = 0 );
  //get model basis term for op
  Node getModelBasisOpTerm( Node op );
  //get model basis
  Node getModelBasis( Node f, Node n );
  //get model basis body
  Node getModelBasisBody( Node f );

//for inst constant
private:
  /** map from universal quantifiers to the list of instantiation constants */
  std::map< Node, std::vector< Node > > d_inst_constants;
  /** map from universal quantifiers to their inst constant body */
  std::map< Node, Node > d_inst_const_body;
  /** map from universal quantifiers to their counterexample literals */
  std::map< Node, Node > d_ce_lit;
  /** instantiation constants to universal quantifiers */
  std::map< Node, Node > d_inst_constants_map;
  /** make instantiation constants for */
  void makeInstantiationConstantsFor( Node f );
public:
  /** get the i^th instantiation constant of f */
  Node getInstantiationConstant( Node f, int i ) { return d_inst_constants[f][i]; }
  /** get number of instantiation constants for f */
  int getNumInstantiationConstants( Node f ) { return (int)d_inst_constants[f].size(); }
  /** get the ce body f[e/x] */
  Node getInstConstantBody( Node f );
  /** get counterexample literal (for cbqi) */
  Node getCounterexampleLiteral( Node f );
  /** returns node n with bound vars of f replaced by instantiation constants of f
      node n : is the futur pattern
      node f : is the quantifier containing which bind the variable
      return a pattern where the variable are replaced by variable for
      instantiation.
   */
  Node getInstConstantNode( Node n, Node f );
  /** same as before but node f is just linked to the new pattern by the
      applied attribute
      vars the bind variable
      nvars the same variable but with an attribute
  */
  Node convertNodeToPattern( Node n, Node f,
                             const std::vector<Node> & vars,
                             const std::vector<Node> & nvars);
  /** get iff term */
  Node getInstConstantIffTerm( Node n, bool pol );
  /** make node, validating the inst constant attribute */
  Node mkNodeInstConstant( Kind k, std::vector< Node >& children, Node f );
  /** set instantiation constant attr */
  void setInstantiationConstantAttr( Node n, Node f );

//for skolem
private:
  /** map from universal quantifiers to the list of skolem constants */
  std::map< Node, std::vector< Node > > d_skolem_constants;
  /** map from universal quantifiers to their skolemized body */
  std::map< Node, Node > d_skolem_body;
public:
  /** get the skolemized body f[e/x] */
  Node getSkolemizedBody( Node f );

//miscellaneous
private:
  /** map from universal quantifiers to the list of variables */
  std::map< Node, std::vector< Node > > d_vars;
  /** free variable for instantiation constant type */
  std::map< TypeNode, Node > d_free_vars;
public:
  /** get free variable for instantiation constant */
  Node getFreeVariableForInstConstant( Node n );
  /** set instantiation level attr */
  void setInstantiationLevelAttr( Node n, uint64_t level );

//for triggers
private:
  /** helper function for compute var contains */
  void computeVarContains2( Node n, Node parent );
  /** var contains */
  std::map< TNode, std::vector< TNode > > d_var_contains;
public:
  /** compute var contains */
  void computeVarContains( Node n );
  /** variables subsume, return true if n1 contains all free variables in n2 */
  bool isVariableSubsume( Node n1, Node n2 );
  /** get var contains for each of the patterns in pats */
  void getVarContains( Node f, std::vector< Node >& pats, std::map< Node, std::vector< Node > >& varContains );
  /** get var contains for node n */
  void getVarContainsNode( Node f, Node n, std::vector< Node >& varContains );
private:
  /** all triggers will be stored in this trie */
  TrTrie d_tr_trie;
public:
  /** get trigger */
  inst::Trigger* getTrigger( std::vector< Node >& nodes ){ return d_tr_trie.getTrigger( nodes ); }
  /** add trigger */
  void addTrigger( std::vector< Node >& nodes, inst::Trigger* t ){ d_tr_trie.addTrigger( nodes, t ); }
};/* class TermDb */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H */
