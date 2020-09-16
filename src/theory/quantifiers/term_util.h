/*********************                                                        */
/*! \file term_util.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief term utilities class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__TERM_UTIL_H
#define CVC4__THEORY__QUANTIFIERS__TERM_UTIL_H

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

//for quantifier instantiation level
struct QuantInstLevelAttributeId {};
typedef expr::Attribute<QuantInstLevelAttributeId, uint64_t> QuantInstLevelAttribute;

/** Attribute for id number */
struct QuantIdNumAttributeId {};
typedef expr::Attribute< QuantIdNumAttributeId, uint64_t > QuantIdNumAttribute;

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
  static Node getRemoveQuantifiers2( Node n, std::map< Node, Node >& visited );
public:
  //remove quantifiers
  static Node getRemoveQuantifiers( Node n );
  //quantified simplify (treat free variables in n as quantified and run rewriter)
  static Node getQuantSimplify( Node n );

 private:
  /** adds the set of nodes of kind k in n to vars */
  static void computeVarContainsInternal(Node n,
                                         Kind k,
                                         std::vector<Node>& vars);

 public:
  /** adds the set of nodes of kind INST_CONSTANT in n to ics */
  static void computeInstConstContains(Node n, std::vector<Node>& ics);
  /** adds the set of nodes of kind BOUND_VARIABLE in n to vars */
  static void computeVarContains(Node n, std::vector<Node>& vars);
  /** adds the set of (top-level) nodes of kind FORALL in n to quants */
  static void computeQuantContains(Node n, std::vector<Node>& quants);
  /**
   * Adds the set of nodes of kind INST_CONSTANT in n that belong to quantified
   * formula q to vars.
   */
  static void computeInstConstContainsForQuant(Node q,
                                               Node n,
                                               std::vector<Node>& vars);

public:
  
//general utilities
  // TODO #1216 : promote these?
 private:
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
  /** contains uninterpreted constant */
  static bool containsUninterpretedConstant( Node n );
  /** get the term depth of n */
  static int getTermDepth( Node n );
  /** simple negate */
  static Node simpleNegate( Node n );
  /** is the kind k a negation kind?
   *
   * A kind k is a negation kind if <k>( <k>( n ) ) = n.
   */
  static bool isNegate(Kind k);
  /**
   * Make negated term, returns the negation of n wrt Kind notk, eliminating
   * double negation if applicable, e.g. mkNegate( ~, ~x ) ---> x.
   */
  static Node mkNegate(Kind notk, Node n);
  /** is k associative?
   *
   * If flag reqNAry is true, then we additionally require that k is an
   * n-ary operator.
   */
  static bool isAssoc(Kind k, bool reqNAry = false);
  /** is k commutative?
   *
   * If flag reqNAry is true, then we additionally require that k is an
   * n-ary operator.
   */
  static bool isComm(Kind k, bool reqNAry = false);

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
   *   <k>( ... t_{arg-1}, n, t_{arg+1}...) = ret
   * always holds for some constant ret, which is returned by this function.
   */
  Node isSingularArg(Node n, Kind ik, unsigned arg);

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
  /**
   * Make const, returns pol ? mkTypeValue(tn,0) : mkTypeMaxValue(tn).
   * In other words, this returns either the minimum element of tn if pol is
   * true, and the maximum element in pol is false. The type tn should have
   * minimum and maximum elements, for example tn is Bool or BitVector.
   */
  static Node mkTypeConst(TypeNode tn, bool pol);
};/* class TermUtil */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__TERM_UTIL_H */
