/*********************                                                        */
/*! \file term_database.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief term database class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H
#define __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H

#include "expr/attribute.h"
#include "theory/theory.h"
#include "theory/type_enumerator.h"
#include "theory/quantifiers/quant_util.h"

#include <map>

namespace CVC4 {
namespace theory {

/** Attribute true for quantifiers that are axioms */
struct AxiomAttributeId {};
typedef expr::Attribute< AxiomAttributeId, bool > AxiomAttribute;

/** Attribute true for quantifiers that are conjecture */
struct ConjectureAttributeId {};
typedef expr::Attribute< ConjectureAttributeId, bool > ConjectureAttribute;

/** Attribute true for function definition quantifiers */
struct FunDefAttributeId {};
typedef expr::Attribute< FunDefAttributeId, bool > FunDefAttribute;

/** Attribute true for quantifiers that are SyGus conjectures */
struct SygusAttributeId {};
typedef expr::Attribute< SygusAttributeId, bool > SygusAttribute;

/** Attribute true for quantifiers that are synthesis conjectures */
struct SynthesisAttributeId {};
typedef expr::Attribute< SynthesisAttributeId, bool > SynthesisAttribute;

// attribute for "contains instantiation constants from"
struct InstConstantAttributeId {};
typedef expr::Attribute<InstConstantAttributeId, Node> InstConstantAttribute;

struct BoundVarAttributeId {};
typedef expr::Attribute<BoundVarAttributeId, Node> BoundVarAttribute;

struct InstLevelAttributeId {};
typedef expr::Attribute<InstLevelAttributeId, uint64_t> InstLevelAttribute;

struct InstVarNumAttributeId {};
typedef expr::Attribute<InstVarNumAttributeId, uint64_t> InstVarNumAttribute;

struct TermDepthAttributeId {};
typedef expr::Attribute<TermDepthAttributeId, uint64_t> TermDepthAttribute;

struct ContainsUConstAttributeId {};
typedef expr::Attribute<ContainsUConstAttributeId, uint64_t> ContainsUConstAttribute;

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

/** Attribute true for quantifiers that do not need to be partially instantiated */
struct LtePartialInstAttributeId {};
typedef expr::Attribute< LtePartialInstAttributeId, bool > LtePartialInstAttribute;

// attribute for "contains instantiation constants from"
struct SygusProxyAttributeId {};
typedef expr::Attribute<SygusProxyAttributeId, Node> SygusProxyAttribute;

//attribute for fun-def abstraction type
struct AbsTypeFunDefAttributeId {};
typedef expr::Attribute<AbsTypeFunDefAttributeId, bool> AbsTypeFunDefAttribute;

/** Attribute true for quantifiers that we are doing quantifier elimination on */
struct QuantElimAttributeId {};
typedef expr::Attribute< QuantElimAttributeId, bool > QuantElimAttribute;

/** Attribute true for quantifiers that we are doing partial quantifier elimination on */
struct QuantElimPartialAttributeId {};
typedef expr::Attribute< QuantElimPartialAttributeId, bool > QuantElimPartialAttribute;

/** Attribute for id number */
struct QuantIdNumAttributeId {};
typedef expr::Attribute< QuantIdNumAttributeId, uint64_t > QuantIdNumAttribute;


class QuantifiersEngine;

namespace inst{
  class Trigger;
}

namespace quantifiers {

class TermArgTrie {
public:
  /** the data */
  std::map< TNode, TermArgTrie > d_data;
public:
  bool hasNodeData() { return !d_data.empty(); }
  TNode getNodeData() { return d_data.begin()->first; }
  TNode existsTerm( std::vector< TNode >& reps, int argIndex = 0 );
  TNode addOrGetTerm( TNode n, std::vector< TNode >& reps, int argIndex = 0 );
  bool addTerm( TNode n, std::vector< TNode >& reps, int argIndex = 0 );
  void debugPrint( const char * c, Node n, unsigned depth = 0 );
  void clear() { d_data.clear(); }
};/* class TermArgTrie */


class QAttributes{
public:
  QAttributes() : d_hasPattern(false), d_conjecture(false), d_axiom(false), d_sygus(false),
                  d_synthesis(false), d_rr_priority(-1), d_qinstLevel(-1), d_quant_elim(false), d_quant_elim_partial(false){}
  ~QAttributes(){}
  bool d_hasPattern;
  Node d_rr;
  bool d_conjecture;
  bool d_axiom;
  Node d_fundef_f;
  bool d_sygus;
  bool d_synthesis;
  int d_rr_priority;
  int d_qinstLevel;
  bool d_quant_elim;
  bool d_quant_elim_partial;
  Node d_ipl;
  Node d_qid_num;
  bool isRewriteRule() { return !d_rr.isNull(); }
  bool isFunDef() { return !d_fundef_f.isNull(); }
};

namespace fmcheck {
  class FullModelChecker;
}

class TermDbSygus;
class QuantConflictFind;
class RelevantDomain;
class ConjectureGenerator;
class TermGenerator;
class TermGenEnv;

class TermDb : public QuantifiersUtil {
  friend class ::CVC4::theory::QuantifiersEngine;
  //TODO: eliminate most of these
  friend class ::CVC4::theory::inst::Trigger;
  friend class ::CVC4::theory::quantifiers::fmcheck::FullModelChecker;
  friend class ::CVC4::theory::quantifiers::QuantConflictFind;
  friend class ::CVC4::theory::quantifiers::RelevantDomain;
  friend class ::CVC4::theory::quantifiers::ConjectureGenerator;
  friend class ::CVC4::theory::quantifiers::TermGenEnv;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
private:
  /** reference to the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  /** terms processed */
  std::hash_set< Node, NodeHashFunction > d_processed;
  /** terms processed */
  std::hash_set< Node, NodeHashFunction > d_iclosure_processed;
  /** select op map */
  std::map< Node, std::map< TypeNode, Node > > d_par_op_map;
  /** whether master equality engine is UF-inconsistent */
  bool d_consistent_ee;

 public:
  TermDb(context::Context* c, context::UserContext* u, QuantifiersEngine* qe);
  ~TermDb();
  /** boolean terms */
  Node d_true;
  Node d_false;
  /** constants */
  Node d_zero;
  Node d_one;

 public:
  /** presolve (called once per user check-sat) */
  void presolve();
  /** reset (calculate which terms are active) */
  bool reset( Theory::Effort effort );
  /** identify */
  std::string identify() const { return "TermDb"; }  
 private:
  /** map from operators to ground terms for that operator */
  std::map< Node, std::vector< Node > > d_op_map;
  /** map from type nodes to terms of that type */
  std::map< TypeNode, std::vector< Node > > d_type_map;
  /** inactive map */
  NodeBoolMap d_inactive_map;

  /** count number of non-redundant ground terms per operator */
  std::map< Node, int > d_op_nonred_count;
  /**mapping from UF terms to representatives of their arguments */
  std::map< TNode, std::vector< TNode > > d_arg_reps;
  /** map from operators to trie */
  std::map< Node, TermArgTrie > d_func_map_trie;
  std::map< Node, TermArgTrie > d_func_map_eqc_trie;
  /** mapping from operators to their representative relevant domains */
  std::map< Node, std::map< unsigned, std::vector< Node > > > d_func_map_rel_dom;
  /** has map */
  std::map< Node, bool > d_has_map;
  /** map from reps to a term in eqc in d_has_map */
  std::map< Node, Node > d_term_elig_eqc;  
  /** set has term */
  void setHasTerm( Node n );
  /** evaluate term */
  Node evaluateTerm2( TNode n, std::map< TNode, Node >& visited, EqualityQuery * qy, bool useEntailmentTests );
  TNode getEntailedTerm2( TNode n, std::map< TNode, TNode >& subs, bool subsRep, bool hasSubs, EqualityQuery * qy );
  bool isEntailed2( TNode n, std::map< TNode, TNode >& subs, bool subsRep, bool hasSubs, bool pol, EqualityQuery * qy );
public:
  /** ground terms for operator */
  unsigned getNumGroundTerms( Node f );
  /** get ground term for operator */
  Node getGroundTerm( Node f, unsigned i );
  /** get num type terms */
  unsigned getNumTypeGroundTerms( TypeNode tn );
  /** get type ground term */
  Node getTypeGroundTerm( TypeNode tn, unsigned i );
  /** add a term to the database */
  void addTerm( Node n, std::set< Node >& added, bool withinQuant = false, bool withinInstClosure = false );
  /** get match operator */
  Node getMatchOperator( Node n );
  /** get term arg index */
  TermArgTrie * getTermArgTrie( Node f );
  TermArgTrie * getTermArgTrie( Node eqc, Node f );
  /** exists term */
  TNode getCongruentTerm( Node f, Node n );
  TNode getCongruentTerm( Node f, std::vector< TNode >& args );
  /** compute arg reps */
  void computeArgReps( TNode n );
  /** compute uf eqc terms */
  void computeUfEqcTerms( TNode f );
  /** compute uf terms */
  void computeUfTerms( TNode f );
  /** in relevant domain */
  bool inRelevantDomain( TNode f, unsigned i, TNode r );
  /** evaluate a term under a substitution.  Return representative in EE if possible.
   * subsRep is whether subs contains only representatives
   */
  Node evaluateTerm( TNode n, EqualityQuery * qy = NULL, bool useEntailmentTests = false );
  /** get entailed term, does not construct new terms, less aggressive */
  TNode getEntailedTerm( TNode n, EqualityQuery * qy = NULL );
  TNode getEntailedTerm( TNode n, std::map< TNode, TNode >& subs, bool subsRep, EqualityQuery * qy = NULL );
  /** is entailed (incomplete check) */
  bool isEntailed( TNode n, bool pol, EqualityQuery * qy = NULL );
  bool isEntailed( TNode n, std::map< TNode, TNode >& subs, bool subsRep, bool pol, EqualityQuery * qy = NULL );
  /** is active */
  bool isTermActive( Node n );
  void setTermInactive( Node n );
  /** has term */
  bool hasTermCurrent( Node n, bool useMode = true );
  /** is term eligble for instantiation? */
  bool isTermEligibleForInstantiation( TNode n, TNode f, bool print = false );
  /** get has term eqc */
  Node getEligibleTermInEqc( TNode r );
  /** is inst closure */
  bool isInstClosure( Node r );
  
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
  Node getModelBasis( Node q, Node n );
  //get model basis body
  Node getModelBasisBody( Node q );

//for inst constant
private:
  /** map from universal quantifiers to the list of variables */
  std::map< Node, std::vector< Node > > d_vars;
  std::map< Node, std::map< Node, unsigned > > d_var_num;
  /** map from universal quantifiers to their inst constant body */
  std::map< Node, Node > d_inst_const_body;
  /** map from universal quantifiers to their counterexample literals */
  std::map< Node, Node > d_ce_lit;
  /** instantiation constants to universal quantifiers */
  std::map< Node, Node > d_inst_constants_map;
  /** make instantiation constants for */
  void makeInstantiationConstantsFor( Node q );
public:
  /** map from universal quantifiers to the list of instantiation constants */
  std::map< Node, std::vector< Node > > d_inst_constants;
  /** get variable number */
  unsigned getVariableNum( Node q, Node v ) { return d_var_num[q][v]; }
  /** get the i^th instantiation constant of q */
  Node getInstantiationConstant( Node q, int i ) const;
  /** get number of instantiation constants for q */
  unsigned getNumInstantiationConstants( Node q ) const;
  /** get the ce body q[e/x] */
  Node getInstConstantBody( Node q );
  /** get counterexample literal (for cbqi) */
  Node getCounterexampleLiteral( Node q );
  /** returns node n with bound vars of q replaced by instantiation constants of q
      node n : is the future pattern
      node q : is the quantifier containing which bind the variable
      return a pattern where the variable are replaced by variable for
      instantiation.
   */
  Node getInstConstantNode( Node n, Node q );
  Node getVariableNode( Node n, Node q );
  /** get substituted node */
  Node getInstantiatedNode( Node n, Node q, std::vector< Node >& terms );

  static Node getInstConstAttr( Node n );
  static bool hasInstConstAttr( Node n );
  static Node getBoundVarAttr( Node n );
  static bool hasBoundVarAttr( Node n );
  
private:
  /** get bound vars */
  static void getBoundVars2( Node n, std::vector< Node >& vars, std::map< Node, bool >& visited );
  /** get bound vars */
  static Node getRemoveQuantifiers2( Node n, std::map< Node, Node >& visited );
public:
  //get the bound variables in this node
  static void getBoundVars( Node n, std::vector< Node >& vars );
  //remove quantifiers
  static Node getRemoveQuantifiers( Node n );
  //quantified simplify (treat free variables in n as quantified and run rewriter)
  static Node getQuantSimplify( Node n );

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
  // closed enumerable type cache
  std::map< TypeNode, bool > d_typ_closed_enum;
  /** may complete */
  std::map< TypeNode, bool > d_may_complete;
public:
  //get nth term for type
  Node getEnumerateTerm( TypeNode tn, unsigned index );
  //does this type have an enumerator that produces constants that are handled by ground theory solvers
  bool isClosedEnumerableType( TypeNode tn );
  // may complete
  bool mayComplete( TypeNode tn );

//for triggers
private:
  /** helper function for compute var contains */
  static void computeVarContains2( Node n, Kind k, std::vector< Node >& varContains, std::map< Node, bool >& visited );
  /** triggers for each operator */
  std::map< Node, std::vector< inst::Trigger* > > d_op_triggers;
  /** helper for is instance of */
  static bool isUnifiableInstanceOf( Node n1, Node n2, std::map< Node, Node >& subs );
  /** -1: n1 is an instance of n2, 1: n1 is an instance of n2 */
  static int isInstanceOf2( Node n1, Node n2, std::vector< Node >& varContains1, std::vector< Node >& varContains2 );
public:
  /** compute var contains */
  static void computeVarContains( Node n, std::vector< Node >& varContains );
  /** get var contains for each of the patterns in pats */
  static void getVarContains( Node f, std::vector< Node >& pats, std::map< Node, std::vector< Node > >& varContains );
  /** get var contains for node n */
  static void getVarContainsNode( Node f, Node n, std::vector< Node >& varContains );
  /** compute quant contains */
  static void computeQuantContains( Node n, std::vector< Node >& quantContains );
  /** -1: n1 is an instance of n2, 1: n1 is an instance of n2 */
  static int isInstanceOf( Node n1, Node n2 );
  /** filter all nodes that have instances */
  static void filterInstances( std::vector< Node >& nodes );
  /** register trigger (for eager quantifier instantiation) */
  void registerTrigger( inst::Trigger* tr, Node op );

//for term ordering
private:
  /** operator id count */
  int d_op_id_count;
  /** map from operators to id */
  std::map< Node, int > d_op_id;
  /** type id count */
  int d_typ_id_count;
  /** map from type to id */
  std::map< TypeNode, int > d_typ_id;
  //free variables
  std::map< TypeNode, std::vector< Node > > d_cn_free_var;
  // get canonical term, return null if it contains a term apart from handled signature
  Node getCanonicalTerm( TNode n, std::map< TypeNode, unsigned >& var_count, std::map< TNode, TNode >& subs, bool apply_torder, 
                         std::map< TNode, Node >& visited );
public:
  /** get id for operator */
  int getIdForOperator( Node op );
  /** get id for type */
  int getIdForType( TypeNode t );
  /** get term order */
  bool getTermOrder( Node a, Node b );
  /** get canonical free variable #i of type tn */
  Node getCanonicalFreeVar( TypeNode tn, unsigned i );
  /** get canonical term */
  Node getCanonicalTerm( TNode n, bool apply_torder = false );

//for virtual term substitution
private:
  Node d_vts_delta;
  std::map< TypeNode, Node > d_vts_inf;
  Node d_vts_delta_free;
  std::map< TypeNode, Node > d_vts_inf_free;
  /** get vts infinity index */
  Node getVtsInfinityIndex( int i, bool isFree = false, bool create = true  );
  /** substitute vts free terms */
  Node substituteVtsFreeTerms( Node n );
public:
  /** get vts delta */
  Node getVtsDelta( bool isFree = false, bool create = true );
  /** get vts infinity */
  Node getVtsInfinity( TypeNode tn, bool isFree = false, bool create = true );
  /** get all vts terms */
  void getVtsTerms( std::vector< Node >& t, bool isFree = false, bool create = true, bool inc_delta = true );
  /** rewrite delta */
  Node rewriteVtsSymbols( Node n );
  /** simple check for contains term */
  bool containsVtsTerm( Node n, bool isFree = false );
  /** simple check for contains term */
  bool containsVtsTerm( std::vector< Node >& n, bool isFree = false );
  /** simple check for contains term */
  bool containsVtsInfinity( Node n, bool isFree = false );
  /** ensure type */
  static Node ensureType( Node n, TypeNode tn );
  /** get ensure type condition */
  static bool getEnsureTypeCondition( Node n, TypeNode tn, std::vector< Node >& cond );
  /** get relevancy condition */
  static void getRelevancyCondition( Node n, std::vector< Node >& cond );
private:
  //helper for contains term
  static bool containsTerm2( Node n, Node t, std::map< Node, bool >& visited );
  static bool containsTerms2( Node n, std::vector< Node >& t, std::map< Node, bool >& visited );
//general utilities
public:
  /** simple check for whether n contains t as subterm */
  static bool containsTerm( Node n, Node t );
  /** simple check for contains term, true if contains at least one term in t */
  static bool containsTerms( Node n, std::vector< Node >& t );
  /** contains uninterpreted constant */
  static bool containsUninterpretedConstant( Node n );
  /** get the term depth of n */
  static int getTermDepth( Node n );
  /** simple negate */
  static Node simpleNegate( Node n );
  /** is assoc */
  static bool isAssoc( Kind k );
  /** is comm */
  static bool isComm( Kind k );
  /** is bool connective */
  static bool isBoolConnective( Kind k );
  /** is bool connective term */
  static bool isBoolConnectiveTerm( TNode n );

//for sygus
private:
  TermDbSygus * d_sygus_tdb;
public:
  TermDbSygus * getTermDatabaseSygus() { return d_sygus_tdb; }

private:
  std::map< Node, bool > d_fun_defs;
public: //general queries concerning quantified formulas wrt modules
  /** is quantifier treated as a rewrite rule? */
  static bool isRewriteRule( Node q );
  /** get the rewrite rule associated with the quanfied formula */
  static Node getRewriteRule( Node q );
  /** is fun def */
  static bool isFunDef( Node q );
  /** is fun def */
  static bool isFunDefAnnotation( Node ipl );
  /** is sygus conjecture */
  static bool isSygusConjecture( Node q );
  /** is sygus conjecture */
  static bool isSygusConjectureAnnotation( Node ipl );
  /** get fun def body */
  static Node getFunDefHead( Node q );
  /** get fun def body */
  static Node getFunDefBody( Node q );
  /** is quant elim annotation */
  static bool isQuantElimAnnotation( Node ipl );
//attributes
private:
  std::map< Node, QAttributes > d_qattr;
  //record attributes
  void computeAttributes( Node q );
public:
  /** is conjecture */
  bool isQAttrConjecture( Node q );
  /** is axiom */
  bool isQAttrAxiom( Node q );
  /** is function definition */
  bool isQAttrFunDef( Node q );
  /** is sygus conjecture */
  bool isQAttrSygus( Node q );
  /** is synthesis conjecture */
  bool isQAttrSynthesis( Node q );
  /** get instantiation level */
  int getQAttrQuantInstLevel( Node q );
  /** get rewrite rule priority */
  int getQAttrRewriteRulePriority( Node q );
  /** is quant elim */
  bool isQAttrQuantElim( Node q );
  /** is quant elim partial */
  bool isQAttrQuantElimPartial( Node q );
  /** get quant id num */
  int getQAttrQuantIdNum( Node q );
  /** get quant id num */
  Node getQAttrQuantIdNumNode( Node q );
  /** compute quantifier attributes */
  static void computeQuantAttributes( Node q, QAttributes& qa );
};/* class TermDb */

class TermDbSygus {
private:
  /** reference to the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  std::map< TypeNode, std::vector< Node > > d_fv;
  std::map< Node, TypeNode > d_fv_stype;
  std::map< Node, int > d_fv_num;
  Node d_true;
  Node d_false;
public:
  TNode getVar( TypeNode tn, int i );
  TNode getVarInc( TypeNode tn, std::map< TypeNode, int >& var_count );
  bool isVar( Node n ) { return d_fv_stype.find( n )!=d_fv_stype.end(); }
  int getVarNum( Node n ) { return d_fv_num[n]; }
private:
  std::map< TypeNode, std::map< int, Node > > d_generic_base;
  std::map< TypeNode, std::vector< Node > > d_generic_templ;
  bool getMatch( Node p, Node n, std::map< int, Node >& s );
  bool getMatch2( Node p, Node n, std::map< int, Node >& s, std::vector< int >& new_s );
public:
  bool getMatch( Node n, TypeNode st, int& index_found, std::vector< Node >& args, int index_exc = -1, int index_start = 0 );
private:
  //information for sygus types
  std::map< TypeNode, TypeNode > d_register;  //stores sygus -> builtin type
  std::map< TypeNode, std::map< int, Kind > > d_arg_kind;
  std::map< TypeNode, std::map< Kind, int > > d_kinds;
  std::map< TypeNode, std::map< int, Node > > d_arg_const;
  std::map< TypeNode, std::map< Node, int > > d_consts;
  std::map< TypeNode, std::map< Node, int > > d_ops;
  std::map< TypeNode, std::map< int, Node > > d_arg_ops;
  std::map< TypeNode, std::vector< int > > d_id_funcs;
  std::map< TypeNode, std::vector< Node > > d_const_list; //sorted list of constants for type
  std::map< TypeNode, unsigned > d_const_list_pos;
  //information for builtin types
  std::map< TypeNode, std::map< int, Node > > d_type_value;
  std::map< TypeNode, Node > d_type_max_value;
  std::map< TypeNode, std::map< Node, std::map< int, Node > > > d_type_value_offset;
  std::map< TypeNode, std::map< Node, std::map< int, int > > > d_type_value_offset_status;
  //normalized map
  std::map< TypeNode, std::map< Node, Node > > d_normalized;
  std::map< TypeNode, std::map< Node, Node > > d_sygus_to_builtin;
  std::map< TypeNode, std::map< Node, Node > > d_builtin_const_to_sygus;
public:
  TermDbSygus( context::Context* c, QuantifiersEngine* qe );
  ~TermDbSygus(){}
  bool reset( Theory::Effort e );
  std::string identify() const { return "TermDbSygus"; }
  
  bool isRegistered( TypeNode tn );
  TypeNode sygusToBuiltinType( TypeNode tn );
  int getKindArg( TypeNode tn, Kind k );
  int getConstArg( TypeNode tn, Node n );
  int getOpArg( TypeNode tn, Node n );
  bool hasKind( TypeNode tn, Kind k );
  bool hasConst( TypeNode tn, Node n );
  bool hasOp( TypeNode tn, Node n );
  Node getArgConst( TypeNode tn, int i );
  Node getArgOp( TypeNode tn, int i );
  Kind getArgKind( TypeNode tn, int i );
  bool isKindArg( TypeNode tn, int i );
  bool isConstArg( TypeNode tn, int i );
  unsigned getNumIdFuncs( TypeNode tn );
  unsigned getIdFuncIndex( TypeNode tn, unsigned i );
  void registerSygusType( TypeNode tn );
  /** get arg type */
  TypeNode getArgType( const DatatypeConstructor& c, int i );
  /** isAntisymmetric */
  bool isAntisymmetric( Kind k, Kind& dk );
  /** is idempotent arg */
  bool isIdempotentArg( Node n, Kind ik, int arg );
  /** is singular arg */
  bool isSingularArg( Node n, Kind ik, int arg );
  /** get offset arg */
  bool hasOffsetArg( Kind ik, int arg, int& offset, Kind& ok );
  /** get value */
  Node getTypeValue( TypeNode tn, int val );
  /** get value */
  Node getTypeValueOffset( TypeNode tn, Node val, int offset, int& status );
  /** get value */
  Node getTypeMaxValue( TypeNode tn );
  TypeNode getSygusTypeForVar( Node v );
  Node getGenericBase( TypeNode tn, const Datatype& dt, int c );
  Node mkGeneric( const Datatype& dt, int c, std::map< TypeNode, int >& var_count, std::map< int, Node >& pre );
  Node sygusToBuiltin( Node n, TypeNode tn );
  Node builtinToSygusConst( Node c, TypeNode tn, int rcons_depth = 0 );
  Node getSygusNormalized( Node n, std::map< TypeNode, int >& var_count, std::map< Node, Node >& subs );
  Node getNormalized( TypeNode t, Node prog, bool do_pre_norm = false, bool do_post_norm = true );
  int getSygusTermSize( Node n );
  /** given a term, construct an equivalent smaller one that respects syntax */
  Node minimizeBuiltinTerm( Node n );
  /** given a term, expand it into more basic components */
  Node expandBuiltinTerm( Node n );
  /** get comparison kind */
  Kind getComparisonKind( TypeNode tn );
  Kind getPlusKind( TypeNode tn, bool is_neg = false );
  bool doCompare( Node a, Node b, Kind k );
  /** get operator kind */
  static Kind getOperatorKind( Node op );
  /** print sygus term */
  static void printSygusTerm( std::ostream& out, Node n, std::vector< Node >& lvs );
  
  /** get anchor */
  static Node getAnchor( Node n );
//for eager instantiation
private:
  std::map< Node, std::map< Node, bool > > d_subterms;
  std::map< Node, std::vector< Node > > d_evals;
  std::map< Node, std::vector< std::vector< Node > > > d_eval_args;
  std::map< Node, std::map< Node, unsigned > > d_node_mv_args_proc;
public:
  void registerEvalTerm( Node n );
  void registerModelValue( Node n, Node v, std::vector< Node >& lems );
};

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H */
