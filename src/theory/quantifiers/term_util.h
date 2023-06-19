/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Term utilities class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__TERM_UTIL_H
#define CVC5__THEORY__QUANTIFIERS__TERM_UTIL_H

#include <map>

#include "expr/attribute.h"
#include "expr/node.h"

namespace cvc5::internal {
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

/**
 * for quantifier instantiation level.
 */
struct QuantInstLevelAttributeId {};
typedef expr::Attribute<QuantInstLevelAttributeId, uint64_t>
    QuantInstLevelAttribute;

/** Attribute for id number */
struct QuantIdNumAttributeId {};
typedef expr::Attribute< QuantIdNumAttributeId, uint64_t > QuantIdNumAttribute;

namespace quantifiers {

// TODO : #1216 split this class, most of the functions in this class should be dispersed to where they are used.
class TermUtil
{
 public:
  TermUtil() {}
  ~TermUtil() {}

  // for inst constant
 public:
  /** Get the index of BOUND_VARIABLE v in quantifier q */
  static size_t getVariableNum(Node q, Node v);

  static Node getInstConstAttr( Node n );
  /**
   * Does n (or its original form) contain instantiation constants? This method
   * is used for determining when a term is ineligible for instantiation.
   *
   * @param n the node to check.
   * @return true if n has instantiation constants.
   */
  static bool hasInstConstAttr(Node n);
  static Node getBoundVarAttr( Node n );
  static bool hasBoundVarAttr( Node n );
  
private:
  /** get bound vars */
  static Node getRemoveQuantifiers2( Node n, std::map< Node, Node >& visited );
public:
  //remove quantifiers
  static Node getRemoveQuantifiers( Node n );

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
  static bool isIdempotentArg(Node n, Kind ik, int arg);

  /** is singular arg
   * Returns true if
   *   <k>( ... t_{arg-1}, n, t_{arg+1}...) = ret
   * always holds for some constant ret, which is returned by this function.
   */
  static Node isSingularArg(Node n, Kind ik, unsigned arg);

  /** get type value with simple value
   * This gets the Node that represents value val for Type tn
   * This is used to get simple values, e.g. -1,0,1,
   * in a uniform way per type.
   */
  static Node mkTypeValue(TypeNode tn, int32_t val);
  /** make type value with simple offset
   * Returns the value of ( val + getTypeValue( tn, offset ) ),
   * where + is the additive operator for the type.
   * Stores the status (0: success, -1: failure) in status.
   */
  static Node mkTypeValueOffset(TypeNode tn,
                                Node val,
                                int32_t offset,
                                int32_t& status);
  /** make the "max" value for type tn
   * For example,
   *   the max value for Bool is true,
   *   the max value for BitVector is 1..1.
   */
  static Node mkTypeMaxValue(TypeNode tn);
  /**
   * Make const, returns pol ? mkTypeValue(tn,0) : mkTypeMaxValue(tn).
   * In other words, this returns either the minimum element of tn if pol is
   * true, and the maximum element in pol is false. The type tn should have
   * minimum and maximum elements, for example tn is Bool or BitVector.
   */
  static Node mkTypeConst(TypeNode tn, bool pol);
};/* class TermUtil */

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__TERM_UTIL_H */
