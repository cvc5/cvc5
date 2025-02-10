/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common functions for dealing with nodes.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__ARITH_UTILITIES_H
#define CVC5__THEORY__ARITH__ARITH_UTILITIES_H

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "expr/subs.h"
#include "util/dense_map.h"
#include "util/integer.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

//Sets of Nodes
typedef std::unordered_set<Node> NodeSet;
typedef std::unordered_set<TNode> TNodeSet;
typedef context::CDHashSet<Node> CDNodeSet;

inline Node mkBoolNode(NodeManager* nm, bool b) { return nm->mkConst<bool>(b); }

/** \f$ k \in {LT, LEQ, EQ, GEQ, GT} \f$ */
inline bool isRelationOperator(Kind k)
{
  switch (k)
  {
    case Kind::LT:
    case Kind::LEQ:
    case Kind::EQUAL:
    case Kind::GEQ:
    case Kind::GT: return true;
    default: return false;
  }
}

/**
 * Given a relational kind, k, return the kind k' s.t.
 * swapping the lefthand and righthand side is equivalent.
 *
 * The following equivalence should hold,
 *   (k l r) <=> (k' r l)
 */
inline Kind reverseRelationKind(Kind k)
{
  switch (k)
  {
    case Kind::LT: return Kind::GT;
    case Kind::LEQ: return Kind::GEQ;
    case Kind::EQUAL: return Kind::EQUAL;
    case Kind::GEQ: return Kind::LEQ;
    case Kind::GT: return Kind::LT;

    default: Unreachable();
  }
}

inline bool evaluateConstantPredicate(Kind k,
                                      const Rational& left,
                                      const Rational& right)
{
  switch (k)
  {
    case Kind::LT: return left < right;
    case Kind::LEQ: return left <= right;
    case Kind::EQUAL: return left == right;
    case Kind::GEQ: return left >= right;
    case Kind::GT: return left > right;
    default: Unreachable(); return true;
  }
}

/**
 * Returns the appropriate coefficient for the infinitesimal given the kind
 * for an arithmetic atom inorder to represent strict inequalities as inequalities.
 *   x < c  becomes  x <= c + (-1) * \f$ \delta \f$
 *   x > c  becomes  x >= x + ( 1) * \f$ \delta \f$
 * Non-strict inequalities have a coefficient of zero.
 */
inline int deltaCoeff(Kind k)
{
  switch (k)
  {
    case Kind::LT: return -1;
    case Kind::GT: return 1;
    default: return 0;
  }
}

/**
 * Given a literal to TheoryArith return a single kind to
 * to indicate its underlying structure.
 * The function returns the following in each case:
 * - (K left right) -> K where is a wildcard for EQUAL, LT, GT, LEQ, or GEQ:
 * - (NOT (EQUAL left right)) -> DISTINCT
 * - (NOT (LEQ left right))   -> GT
 * - (NOT (GEQ left right))   -> LT
 * - (NOT (LT left right))    -> GEQ
 * - (NOT (GT left right))    -> LEQ
 * If none of these match, it returns UNDEFINED_KIND.
 */
inline Kind oldSimplifiedKind(TNode literal)
{
  switch (literal.getKind())
  {
    case Kind::LT:
    case Kind::GT:
    case Kind::LEQ:
    case Kind::GEQ:
    case Kind::EQUAL: return literal.getKind();
    case Kind::NOT:
    {
      TNode atom = literal[0];
      switch (atom.getKind())
      {
        case Kind::LEQ:  //(not (LEQ x c)) <=> (GT x c)
          return Kind::GT;
        case Kind::GEQ:  //(not (GEQ x c)) <=> (LT x c)
          return Kind::LT;
        case Kind::LT:  //(not (LT x c)) <=> (GEQ x c)
          return Kind::GEQ;
        case Kind::GT:  //(not (GT x c) <=> (LEQ x c)
          return Kind::LEQ;
        case Kind::EQUAL: return Kind::DISTINCT;
        default: Unreachable(); return Kind::UNDEFINED_KIND;
      }
    }
    default: Unreachable(); return Kind::UNDEFINED_KIND;
  }
}

inline Kind negateKind(Kind k){
  switch(k){
    case Kind::LT: return Kind::GEQ;
    case Kind::GT: return Kind::LEQ;
    case Kind::LEQ: return Kind::GT;
    case Kind::GEQ: return Kind::LT;
    case Kind::EQUAL: return Kind::DISTINCT;
    case Kind::DISTINCT: return Kind::EQUAL;
    default: return Kind::UNDEFINED_KIND;
  }
}

inline Node negateConjunctionAsClause(TNode conjunction){
  Assert(conjunction.getKind() == Kind::AND);
  NodeBuilder orBuilder(conjunction.getNodeManager(), Kind::OR);

  for(TNode::iterator i = conjunction.begin(), end=conjunction.end(); i != end; ++i){
    TNode child = *i;
    Node negatedChild = NodeBuilder(conjunction.getNodeManager(), Kind::NOT)
                        << (child);
    orBuilder << negatedChild;
  }
  return orBuilder;
}

inline Node maybeUnaryConvert(NodeBuilder& builder)
{
  Assert(builder.getKind() == Kind::OR || builder.getKind() == Kind::AND
         || builder.getKind() == Kind::ADD || builder.getKind() == Kind::MULT);
  Assert(builder.getNumChildren() >= 1);
  if(builder.getNumChildren() == 1){
    return builder[0];
  }else{
    return builder;
  }
}

inline void flattenAnd(Node n, std::vector<TNode>& out){
  Assert(n.getKind() == Kind::AND);
  for(Node::iterator i=n.begin(), i_end=n.end(); i != i_end; ++i){
    Node curr = *i;
    if (curr.getKind() == Kind::AND)
    {
      flattenAnd(curr, out);
    }
    else
    {
      out.push_back(curr);
    }
  }
}

inline Node flattenAnd(Node n){
  std::vector<TNode> out;
  flattenAnd(n, out);
  return NodeManager::currentNM()->mkNode(Kind::AND, out);
}

/** Make zero of the given type */
Node mkZero(const TypeNode& tn);

/** Is n (integer or real) zero? */
bool isZero(const Node& n);

/** Make one of the given type, maybe negated */
Node mkOne(const TypeNode& tn, bool isNeg = false);

// Returns an node that is the identity of a select few kinds.
inline Node getIdentityType(const TypeNode& tn, Kind k)
{
  switch (k)
  {
    case Kind::ADD: return mkZero(tn);
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
      return NodeManager::currentNM()->mkConstRealOrInt(tn, 1);
    default: Unreachable(); return Node::null();  // silence warning
  }
}

inline Node mkAndFromBuilder(NodeManager* nm, NodeBuilder& nb)
{
  Assert(nb.getKind() == Kind::AND);
  switch (nb.getNumChildren()) {
    case 0: return mkBoolNode(nm, true);
    case 1:
      return nb[0];
    default:
      return (Node)nb;
  }
}

inline Node safeConstructNaryType(const TypeNode& tn,
                                  Kind k,
                                  const std::vector<Node>& children)
{
  switch (children.size())
  {
    case 0: return getIdentityType(tn, k);
    case 1: return children[0];
    default: return NodeManager::currentNM()->mkNode(k, children);
  }
}

// Returns the multiplication of a and b.
inline Node mkMult(Node a, Node b) {
  return NodeManager::mkNode(Kind::MULT, a, b);
}

// Return a constraint that is equivalent to term being is in the range
// [start, end). This includes start and excludes end.
inline Node mkInRange(Node term, Node start, Node end) {
  Node above_start = NodeManager::mkNode(Kind::LEQ, start, term);
  Node below_end = NodeManager::mkNode(Kind::LT, term, end);
  return NodeManager::mkNode(Kind::AND, above_start, below_end);
}

// Creates an expression that constrains q to be equal to one of two expressions
// when n is 0 or not. Useful for division by 0 logic.
//   (ite (= n 0) (= q if_zero) (= q not_zero))
inline Node mkOnZeroIte(Node n, Node q, Node if_zero, Node not_zero) {
  Node zero = mkZero(n.getType());
  return n.eqNode(zero).iteNode(q.eqNode(if_zero), q.eqNode(not_zero));
}

inline Node mkPi(NodeManager* nm)
{
  return nm->mkNullaryOperator(nm->realType(), Kind::PI);
}
/** Join kinds, where k1 and k2 are arithmetic relations returns an
 * arithmetic relation ret such that
 * if (a <k1> b) and (a <k2> b), then (a <ret> b).
 */
Kind joinKinds(Kind k1, Kind k2);

/** Transitive kinds, where k1 and k2 are arithmetic relations returns an
 * arithmetic relation ret such that
 * if (a <k1> b) and (b <k2> c) then (a <ret> c).
 */
Kind transKinds(Kind k1, Kind k2);

/** Is k a transcendental function kind? */
bool isTranscendentalKind(Kind k);
/**
 * Get a lower/upper approximation of the constant r within the given
 * level of precision. In other words, this returns a constant c' such that
 *   c' <= c <= c' + 1/(10^prec) if isLower is true, or
 *   c' + 1/(10^prec) <= c <= c' if isLower is false.
 * where c' is a rational of the form n/d for some n and d <= 10^prec.
 */
Node getApproximateConstant(Node c, bool isLower, unsigned prec);

/** print rational approximation of cr with precision prec on trace c */
void printRationalApprox(const char* c, Node cr, unsigned prec = 5);

/** Make the node u >= a ^ a >= l */
Node mkBounded(Node l, Node a, Node u);

Rational leastIntGreaterThan(const Rational&);

Rational greatestIntLessThan(const Rational&);

/** Negates a node in arithmetic proof normal form. */
Node negateProofLiteral(TNode n);

/**
 * Return the result of multiplying constant integer or real nodes c1 and c2.
 * The returned type is real if either have type real.
 */
Node multConstants(const Node& c1, const Node& c2);

/**
 * Make the equality (= a b) or (= (- a b) zero) if a and b have different
 * types, where zero has the same type as (- a b).
 * Use this utility to ensure an equality is properly typed.
 */
Node mkEquality(const Node& a, const Node& b);

/**
 * Return the real cast of n. If n is a constant integer, we return a
 * constant real. Otherwise we apply TO_REAL to n.
 */
Node castToReal(NodeManager* nm, const Node& n);

/**
 * Ensures that the returned pair has equal type, where a and b have
 * real or integer type. We add TO_REAL if not.
 */
std::pair<Node,Node> mkSameType(const Node& a, const Node& b);

/**
 * Returns the rewritten form of node, which is a term of the form bv2nat(x).
 * The return value of this method is the integer sum:
 *   (+ ite( (= ((_ extract (n-1) (n-1)) x) 1) (^ 2 (n-1)) 0)
 *      ...
 *      ite( (= ((_ extract 0 0) x) 1) (^ 2 0) 0))
 * where n is the bitwidth of x.
 */
Node eliminateBv2Nat(TNode node);
/**
 * Returns the rewritten form of node, which is a term of the form int2bv(x).
 * The return value of this method is the concatenation term:
 *   (bvconcat ite( (>= (mod x (^ 2 n)) (^ 2 (n-1))) (_ bv1 1) (_ bv1 0))
 *             ...
 *             ite( (>= (mod x (^ 2 1)) (^ 2 0)) (_ bv1 1) (_ bv1 0)))
 * where n is the bit-width of x.
 */
Node eliminateInt2Bv(TNode node);

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__ARITH_UTILITIES_H */
