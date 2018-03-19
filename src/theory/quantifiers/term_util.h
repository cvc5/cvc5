/*********************                                                        */
/*! \file term_util.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief term utilities class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__TERM_UTIL_H
#define __CVC4__THEORY__QUANTIFIERS__TERM_UTIL_H

#include <map>
#include <unordered_set>

#include "expr/attribute.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {

// attribute for "contains instantiation constants from"
struct InstConstantAttributeId {};
typedef expr::Attribute<InstConstantAttributeId, Node> InstConstantAttribute;

struct BoundVarAttributeId {};
typedef expr::Attribute<BoundVarAttributeId, Node> BoundVarAttribute;

struct InstVarNumAttributeId {};
typedef expr::Attribute<InstVarNumAttributeId, uint64_t> InstVarNumAttribute;

struct TermDepthAttributeId {};
typedef expr::Attribute<TermDepthAttributeId, uint64_t> TermDepthAttribute;

struct ContainsUConstAttributeId {};
typedef expr::Attribute<ContainsUConstAttributeId, uint64_t> ContainsUConstAttribute;

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

// attribute for associating a synthesis function with a first order variable
struct SygusSynthGrammarAttributeId {};
typedef expr::Attribute<SygusSynthGrammarAttributeId, Node>
    SygusSynthGrammarAttribute;

// attribute for associating a variable list with a synth fun
struct SygusSynthFunVarListAttributeId {};
typedef expr::Attribute<SygusSynthFunVarListAttributeId, Node> SygusSynthFunVarListAttribute;

//attribute for fun-def abstraction type
struct AbsTypeFunDefAttributeId {};
typedef expr::Attribute<AbsTypeFunDefAttributeId, bool> AbsTypeFunDefAttribute;

/** Attribute for id number */
struct QuantIdNumAttributeId {};
typedef expr::Attribute< QuantIdNumAttributeId, uint64_t > QuantIdNumAttribute;

/** sygus var num */
struct SygusVarNumAttributeId {};
typedef expr::Attribute<SygusVarNumAttributeId, uint64_t> SygusVarNumAttribute;

/** Attribute to mark Skolems as virtual terms */
struct VirtualTermSkolemAttributeId {};
typedef expr::Attribute< VirtualTermSkolemAttributeId, bool > VirtualTermSkolemAttribute;

class QuantifiersEngine;

namespace inst{
  class Trigger;
  class HigherOrderTrigger;
}

namespace quantifiers {

class TermDatabase;
class Instantiate;

// TODO : #1216 split this class, most of the functions in this class should be dispersed to where they are used.
class TermUtil : public QuantifiersUtil
{
  // TODO : remove these
  friend class ::CVC4::theory::QuantifiersEngine;
  friend class Instantiate;

 private:
  /** reference to the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
public:
  TermUtil(QuantifiersEngine * qe);
  ~TermUtil();
  /** boolean terms */
  Node d_true;
  Node d_false;
  /** constants */
  Node d_zero;
  Node d_one;

  /** reset */
  bool reset(Theory::Effort e) override { return true; }
  /** register quantifier */
  void registerQuantifier(Node q) override;
  /** identify */
  std::string identify() const override { return "TermUtil"; }
  // for inst constant
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
  Node substituteBoundVariablesToInstConstants(Node n, Node q);
  /** substitute { instantiation constants of q -> bound variables of q } in n
   */
  Node substituteInstConstantsToBoundVariables(Node n, Node q);
  /** substitute { variables of q -> terms } in n */
  Node substituteBoundVariables(Node n, Node q, std::vector<Node>& terms);
  /** substitute { instantiation constants of q -> terms } in n */
  Node substituteInstConstants(Node n, Node q, std::vector<Node>& terms);

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

 private:
  /** helper function for compute var contains */
  static void computeVarContains2( Node n, Kind k, std::vector< Node >& varContains, std::map< Node, bool >& visited );
 public:
  /** compute var contains */
  static void computeVarContains( Node n, std::vector< Node >& varContains );
  /** get var contains for each of the patterns in pats */
  static void getVarContains( Node f, std::vector< Node >& pats, std::map< Node, std::vector< Node > >& varContains );
  /** get var contains for node n */
  static void getVarContainsNode( Node f, Node n, std::vector< Node >& varContains );
  /** compute quant contains */
  static void computeQuantContains( Node n, std::vector< Node >& quantContains );
  // TODO (#1216) : this should be in trigger.h
  /** filter all nodes that have instances */
  static void filterInstances( std::vector< Node >& nodes );

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
  /** get relevancy condition */
  static void getRelevancyCondition( Node n, std::vector< Node >& cond );
  
//general utilities
  // TODO #1216 : promote these?
 private:
  //helper for contains term
  static bool containsTerm2( Node n, Node t, std::map< Node, bool >& visited );
  static bool containsTerms2( Node n, std::vector< Node >& t, std::map< Node, bool >& visited );
  /** cache for getTypeValue */
  std::unordered_map<TypeNode,
                     std::unordered_map<int, Node>,
                     TypeNodeHashFunction>
      d_type_value;
  /** cache for getTypeMaxValue */
  std::unordered_map<TypeNode, Node, TypeNodeHashFunction> d_type_max_value;
  /** cache for getTypeValueOffset */
  std::unordered_map<TypeNode,
                     std::unordered_map<Node,
                                        std::unordered_map<int, Node>,
                                        NodeHashFunction>,
                     TypeNodeHashFunction>
      d_type_value_offset;
  /** cache for status of getTypeValueOffset*/
  std::unordered_map<TypeNode,
                     std::unordered_map<Node,
                                        std::unordered_map<int, int>,
                                        NodeHashFunction>,
                     TypeNodeHashFunction>
      d_type_value_offset_status;

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
  /** is k commutative? */
  static bool isComm( Kind k );

  /** is k non-additive?
   * Returns true if
   *   <k>( <k>( T1, x, T2 ), x ) =
   *   <k>( T1, x, T2 )
   * always holds, where T1 and T2 are vectors.
   */
  static bool isNonAdditive( Kind k );
  /** is k a bool connective? */
  static bool isBoolConnective( Kind k );
  /** is n a bool connective term? */
  static bool isBoolConnectiveTerm( TNode n );

  /** is the kind k antisymmetric?
   * If so, return true and store its inverse kind in dk.
   */
  static bool isAntisymmetric(Kind k, Kind& dk);

  /** has offset arg
   * Returns true if there is a Kind ok and offset
   * such that
   *   <ik>( ... t_{arg-1}, n, t_{arg+1}... ) =
   *   <ok>( ... t_{arg-1}, n+offset, t_{arg+1}...)
   * always holds.
   * If so, this function returns true and stores
   * offset and ok in the respective fields.
   */
  static bool hasOffsetArg(Kind ik, int arg, int& offset, Kind& ok);

  /** is idempotent arg
   * Returns true if
   *   <k>( ... t_{arg-1}, n, t_{arg+1}...) =
   *   <k>( ... t_{arg-1}, t_{arg+1}...)
   * always holds.
   */
  bool isIdempotentArg(Node n, Kind ik, int arg);

  /** is singular arg
   * Returns true if
   *   <k>( ... t_{arg-1}, n, t_{arg+1}...) = n
   * always holds.
   */
  Node isSingularArg(Node n, Kind ik, int arg);

  /** get type value
   * This gets the Node that represents value val for Type tn
   * This is used to get simple values, e.g. -1,0,1,
   * in a uniform way per type.
   */
  Node getTypeValue(TypeNode tn, int val);

  /** get type value offset
   * Returns the value of ( val + getTypeValue( tn, offset ) ),
   * where + is the additive operator for the type.
   * Stores the status (0: success, -1: failure) in status.
   */
  Node getTypeValueOffset(TypeNode tn, Node val, int offset, int& status);

  /** get the "max" value for type tn
   * For example,
   *   the max value for Bool is true,
   *   the max value for BitVector is 1..1.
   */
  Node getTypeMaxValue(TypeNode tn);

  /** make value, static version of get value */
  static Node mkTypeValue(TypeNode tn, int val);
  /** make value offset, static version of get value offset */
  static Node mkTypeValueOffset(TypeNode tn, Node val, int offset, int& status);
  /** make max value, static version of get max value */
  static Node mkTypeMaxValue(TypeNode tn);

  // for higher-order
 private:
  /** dummy predicate that states terms should be considered first-class members of equality engine */
  std::map< TypeNode, Node > d_ho_type_match_pred;
public:
  /** get higher-order type match predicate
   * This predicate is used to force certain functions f of type tn to appear as first-class representatives in the
   * quantifier-free UF solver. For a typical use case, we call getHoTypeMatchPredicate which returns a fresh 
   * predicate P of type (tn -> Bool). Then, we add P( f ) as a lemma.  
   * TODO: we may eliminate this depending on how github issue #1115 is resolved.
   */
  Node getHoTypeMatchPredicate( TypeNode tn );
};/* class TermUtil */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__TERM_UTIL_H */
