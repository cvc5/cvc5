/*********************                                                        */
/*! \file term_database.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief term database class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H
#define __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H

#include "expr/attribute.h"
#include "theory/theory.h"

#include <map>

namespace CVC4 {
namespace theory {

/** Attribute true for nodes that should not be used for matching */
struct NoMatchAttributeId {};
/** use the special for boolean flag */
typedef expr::Attribute< NoMatchAttributeId,
                         bool,
                         expr::attr::NullCleanupStrategy,
                         true // context dependent
                       > NoMatchAttribute;

// attribute for "contains instantiation constants from"
struct InstConstantAttributeId {};
typedef expr::Attribute<InstConstantAttributeId, Node> InstConstantAttribute;

struct InstLevelAttributeId {};
typedef expr::Attribute<InstLevelAttributeId, uint64_t> InstLevelAttribute;

struct InstVarNumAttributeId {};
typedef expr::Attribute<InstVarNumAttributeId, uint64_t> InstVarNumAttribute;

// Attribute that tell if a node have been asserted in this branch
struct AvailableInTermDbId {};
/** use the special for boolean flag */
typedef expr::Attribute<AvailableInTermDbId,
                        bool,
                        expr::attr::NullCleanupStrategy,
                        true  // context dependent
                        > AvailableInTermDb;

struct ModelBasisAttributeId {};
typedef expr::Attribute<ModelBasisAttributeId, bool> ModelBasisAttribute;
//for APPLY_UF terms, 1 : term has direct child with model basis attribute,
//                    0 : term has no direct child with model basis attribute.
struct ModelBasisArgAttributeId {};
typedef expr::Attribute<ModelBasisArgAttributeId, uint64_t> ModelBasisArgAttribute;

struct HasBoundVarAttributeId {};
typedef expr::Attribute<HasBoundVarAttributeId, bool> HasBoundVarAttribute;
struct HasBoundVarComputedAttributeId {};
typedef expr::Attribute<HasBoundVarComputedAttributeId, bool> HasBoundVarComputedAttribute;

//for rewrite rules
struct QRewriteRuleAttributeId {};
typedef expr::Attribute<QRewriteRuleAttributeId, Node> QRewriteRuleAttribute;

//for bounded integers
struct BoundIntLitAttributeId {};
typedef expr::Attribute<BoundIntLitAttributeId, uint64_t> BoundIntLitAttribute;


class QuantifiersEngine;

namespace inst{
  class Trigger;
}
namespace rrinst{
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


namespace fmcheck {
  class FullModelChecker;
}

class TermDb {
  friend class ::CVC4::theory::QuantifiersEngine;
  friend class ::CVC4::theory::inst::Trigger;
  friend class ::CVC4::theory::rrinst::Trigger;
  friend class ::CVC4::theory::quantifiers::fmcheck::FullModelChecker;
private:
  /** reference to the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  /** terms processed */
  std::hash_set< Node, NodeHashFunction > d_processed;
private:
  /** select op map */
  std::map< Node, std::map< TypeNode, std::map< TypeNode, Node > > > d_par_op_map;
public:
  TermDb( QuantifiersEngine* qe ) : d_quantEngine( qe ){}
  ~TermDb(){}
  /** map from APPLY_UF operators to ground terms for that operator */
  std::map< Node, std::vector< Node > > d_op_map;
  /** count number of APPLY_UF terms per operator */
  std::map< Node, int > d_op_count;
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
  /** get operation */
  Node getOperator( Node n );
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
  Node getInstantiationConstant( Node f, int i ) const;
  /** get number of instantiation constants for f */
  int getNumInstantiationConstants( Node f ) const;
  /** get the ce body f[e/x] */
  Node getInstConstantBody( Node f );
  /** get counterexample literal (for cbqi) */
  Node getCounterexampleLiteral( Node f );
  /** returns node n with bound vars of f replaced by instantiation constants of f
      node n : is the future pattern
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

  static Node getInstConstAttr( Node n );
  static bool hasInstConstAttr( Node n );
//for bound variables
public:
  //does n have bound variables?
  static bool hasBoundVarAttr( Node n );
  //get bound variables in n
  static void getBoundVars( Node n, std::vector< Node >& bvs);
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

//for triggers
private:
  /** helper function for compute var contains */
  void computeVarContains2( Node n, Node parent );
  /** var contains */
  std::map< TNode, std::vector< TNode > > d_var_contains;
  /** triggers for each operator */
  std::map< Node, std::vector< inst::Trigger* > > d_op_triggers;
  /** helper for is instance of */
  bool isUnifiableInstanceOf( Node n1, Node n2, std::map< Node, Node >& subs );
public:
  /** compute var contains */
  void computeVarContains( Node n );
  /** variables subsume, return true if n1 contains all free variables in n2 */
  bool isVariableSubsume( Node n1, Node n2 );
  /** get var contains for each of the patterns in pats */
  void getVarContains( Node f, std::vector< Node >& pats, std::map< Node, std::vector< Node > >& varContains );
  /** get var contains for node n */
  void getVarContainsNode( Node f, Node n, std::vector< Node >& varContains );
  /** register trigger (for eager quantifier instantiation) */
  void registerTrigger( inst::Trigger* tr, Node op );
  /** -1: n1 is an instance of n2, 1: n1 is an instance of n2 */
  int isInstanceOf( Node n1, Node n2 );
  /** filter all nodes that have instances */
  void filterInstances( std::vector< Node >& nodes );
};/* class TermDb */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H */
