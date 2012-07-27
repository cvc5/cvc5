/**********************/
/*! \file term_database.h
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
 ** \brief term database class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__QUANTIFIERS_TERM_DATABASE_H
#define __CVC4__QUANTIFIERS_TERM_DATABASE_H

#include "theory/theory.h"

#include <map>

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

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

class TermDb {
  friend class ::CVC4::theory::QuantifiersEngine;
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
private:
  //map from types to model basis terms
  std::map< TypeNode, Node > d_model_basis_term;
  //map from ops to model basis terms
  std::map< Node, Node > d_model_basis_op_term;
  //map from instantiation terms to their model basis equivalent
  std::map< Node, Node > d_model_basis;
public:
  //get model basis term
  Node getModelBasisTerm( TypeNode tn, int i = 0 );
  //get model basis term for op
  Node getModelBasisOpTerm( Node op );
  // compute model basis arg
  void computeModelBasisArgAttribute( Node n );
  //register instantiation terms with their corresponding model basis terms
  void registerModelBasis( Node n, Node gn );
  //get model basis
  Node getModelBasis( Node n ) { return d_model_basis[n]; }
private:
  /** map from universal quantifiers to the list of variables */
  std::map< Node, std::vector< Node > > d_vars;
  /** map from universal quantifiers to the list of skolem constants */
  std::map< Node, std::vector< Node > > d_skolem_constants;
  /** map from universal quantifiers to their skolemized body */
  std::map< Node, Node > d_skolem_body;
  /** instantiation constants to universal quantifiers */
  std::map< Node, Node > d_inst_constants_map;
  /** map from universal quantifiers to their counterexample body */
  std::map< Node, Node > d_counterexample_body;
  /** free variable for instantiation constant type */
  std::map< TypeNode, Node > d_free_vars;
private:
  /** make instantiation constants for */
  void makeInstantiationConstantsFor( Node f );
public:
  /** map from universal quantifiers to the list of instantiation constants */
  std::map< Node, std::vector< Node > > d_inst_constants;
  /** set instantiation level attr */
  void setInstantiationLevelAttr( Node n, uint64_t level );
  /** set instantiation constant attr */
  void setInstantiationConstantAttr( Node n, Node f );
  /** get the i^th instantiation constant of f */
  Node getInstantiationConstant( Node f, int i ) { return d_inst_constants[f][i]; }
  /** get number of instantiation constants for f */
  int getNumInstantiationConstants( Node f ) { return (int)d_inst_constants[f].size(); }
  /** get the ce body f[e/x] */
  Node getCounterexampleBody( Node f );
  /** get the skolemized body f[e/x] */
  Node getSkolemizedBody( Node f );
  /** returns node n with bound vars of f replaced by instantiation constants of f
      node n : is the futur pattern
      node f : is the quantifier containing which bind the variable
      return a pattern where the variable are replaced by variable for
      instantiation.
   */
  Node getSubstitutedNode( Node n, Node f );
  /** same as before but node f is just linked to the new pattern by the
      applied attribute
      vars the bind variable
      nvars the same variable but with an attribute
  */
  Node convertNodeToPattern( Node n, Node f,
                             const std::vector<Node> & vars,
                             const std::vector<Node> & nvars);
  /** get free variable for instantiation constant */
  Node getFreeVariableForInstConstant( Node n );
};/* class TermDb */

}
}
}

#endif
