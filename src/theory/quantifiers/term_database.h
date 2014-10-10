/*********************                                                        */
/*! \file term_database.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
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
#include "theory/type_enumerator.h"

#include <map>

namespace CVC4 {
namespace theory {

/** Attribute true for quantifiers that are axioms */
struct AxiomAttributeId {};
typedef expr::Attribute< AxiomAttributeId, bool > AxiomAttribute;

/** Attribute true for quantifiers that are conjecture */
struct ConjectureAttributeId {};
typedef expr::Attribute< ConjectureAttributeId, bool > ConjectureAttribute;
  
/** Attribute true for quantifiers that are SyGus conjectures */
struct SygusAttributeId {};
typedef expr::Attribute< SygusAttributeId, bool > SygusAttribute;

/** Attribute true for quantifiers that are synthesis conjectures */
struct SynthesisAttributeId {};
typedef expr::Attribute< SynthesisAttributeId, bool > SynthesisAttribute;

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

struct ModelBasisAttributeId {};
typedef expr::Attribute<ModelBasisAttributeId, bool> ModelBasisAttribute;
//for APPLY_UF terms, 1 : term has direct child with model basis attribute,
//                    0 : term has no direct child with model basis attribute.
struct ModelBasisArgAttributeId {};
typedef expr::Attribute<ModelBasisArgAttributeId, uint64_t> ModelBasisArgAttribute;

//for bounded integers
struct BoundIntLitAttributeId {};
typedef expr::Attribute<BoundIntLitAttributeId, uint64_t> BoundIntLitAttribute;

//for quantifier instantiation level
struct QuantInstLevelAttributeId {};
typedef expr::Attribute<QuantInstLevelAttributeId, uint64_t> QuantInstLevelAttribute;

//rewrite-rule priority
struct RrPriorityAttributeId {};
typedef expr::Attribute<RrPriorityAttributeId, uint64_t> RrPriorityAttribute;

class QuantifiersEngine;

namespace inst{
  class Trigger;
}
namespace rrinst{
  class Trigger;
}


namespace quantifiers {

class TermArgTrie {
public:
  /** the data */
  std::map< TNode, TermArgTrie > d_data;
public:
  TNode existsTerm( std::vector< TNode >& reps, int argIndex = 0 );
  bool addTerm( TNode n, std::vector< TNode >& reps, int argIndex = 0 );
  void debugPrint( const char * c, Node n, unsigned depth = 0 );
  void clear() { d_data.clear(); }
};/* class TermArgTrie */


namespace fmcheck {
  class FullModelChecker;
}

class TermDb {
  friend class ::CVC4::theory::QuantifiersEngine;
  friend class ::CVC4::theory::inst::Trigger;
  friend class ::CVC4::theory::rrinst::Trigger;
  friend class ::CVC4::theory::quantifiers::fmcheck::FullModelChecker;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;
private:
  /** reference to the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  /** terms processed */
  std::hash_set< Node, NodeHashFunction > d_processed;
private:
  /** select op map */
  std::map< Node, std::map< TypeNode, Node > > d_par_op_map;
  /** count number of ground terms per operator (user-context dependent) */
  NodeIntMap d_op_ccount;
public:
  TermDb( context::Context* c, context::UserContext* u, QuantifiersEngine* qe );
  ~TermDb(){}
  /** boolean terms */
  Node d_true;
  Node d_false;
  /** ground terms */
  unsigned getNumGroundTerms( Node f );
  /** count number of non-redundant ground terms per operator */
  std::map< Node, int > d_op_nonred_count;
  /** map from APPLY_UF operators to ground terms for that operator */
  std::map< Node, std::vector< Node > > d_op_map;
  /** map from APPLY_UF functions to trie */
  std::map< Node, TermArgTrie > d_func_map_trie;
  std::map< Node, TermArgTrie > d_func_map_eqc_trie;
  /**mapping from UF terms to representatives of their arguments */
  std::map< TNode, std::vector< TNode > > d_arg_reps;
  /** map from type nodes to terms of that type */
  std::map< TypeNode, std::vector< Node > > d_type_map;
  /** add a term to the database */
  void addTerm( Node n, std::set< Node >& added, bool withinQuant = false );
  /** reset (calculate which terms are active) */
  void reset( Theory::Effort effort );
  /** get operator*/
  Node getOperator( Node n );
  /** get term arg index */
  TermArgTrie * getTermArgTrie( Node f );
  TermArgTrie * getTermArgTrie( Node eqc, Node f );
  /** exists term */
  TNode existsTerm( Node f, Node n );
  /** compute arg reps */
  void computeArgReps( TNode n );
  /** compute uf eqc terms */
  void computeUfEqcTerms( TNode f );
  /** evaluate a term under a substitution.  Return representative in EE if possible.
   * subsRep is whether subs contains only representatives
   */
  TNode evaluateTerm( TNode n, std::map< TNode, TNode >& subs, bool subsRep );
  /** same as above, but without substitution */
  TNode evaluateTerm( TNode n );
  /** is entailed (incomplete check) */
  bool isEntailed( TNode n, std::map< TNode, TNode >& subs, bool subsRep, bool pol );
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
  //get bound variables in n
  static void getBoundVars( Node n, std::vector< Node >& bvs);
  
  
//for skolem
private:
  /** map from universal quantifiers to their skolemized body */
  std::map< Node, Node > d_skolem_body;
public:
  /** map from universal quantifiers to the list of skolem constants */
  std::map< Node, std::vector< Node > > d_skolem_constants;
  /** make the skolemized body f[e/x] */
  static Node mkSkolemizedBody( Node f, Node n, std::vector< TypeNode >& fvTypes, std::vector< TNode >& fvs,
                                std::vector< Node >& sk, Node& sub, std::vector< unsigned >& sub_vars );
  /** get the skolemized body */
  Node getSkolemizedBody( Node f);
  /** is induction variable */
  static bool isInductionTerm( Node n );
  
//for ground term enumeration
private:  
  /** ground terms enumerated for types */
  std::map< TypeNode, std::vector< Node > > d_enum_terms;
  //type enumerators
  std::map< TypeNode, unsigned > d_typ_enum_map;
  std::vector< TypeEnumerator > d_typ_enum;
public:
  //get nth term for type
  Node getEnumerateTerm( TypeNode tn, unsigned index );  
  
//miscellaneous
public:
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

  
public: //general queries concerning quantified formulas wrt modules
  /** is quantifier treated as a rewrite rule? */
  static bool isRewriteRule( Node q );
  /** get the rewrite rule associated with the quanfied formula */
  static Node getRewriteRule( Node q );
  
//attributes
private:
  std::map< Node, bool > d_qattr_conjecture;
  std::map< Node, bool > d_qattr_axiom;
  std::map< Node, bool > d_qattr_sygus;
  std::map< Node, bool > d_qattr_synthesis;
  std::map< Node, int > d_qattr_rr_priority;
  std::map< Node, int > d_qattr_qinstLevel;
  //record attributes
  void computeAttributes( Node q );
public:
  /** is conjecture */
  bool isQAttrConjecture( Node q );
  /** is axiom */
  bool isQAttrAxiom( Node q );
  /** is sygus conjecture */
  bool isQAttrSygus( Node q );
  /** is synthesis conjecture */
  bool isQAttrSynthesis( Node q );
  /** get instantiation level */
  int getQAttrQuantInstLevel( Node q );
  /** get rewrite rule priority */
  int getQAttrRewriteRulePriority( Node q );
  
};/* class TermDb */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H */
