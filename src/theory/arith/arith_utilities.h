/*********************                                                        */
/*! \file arith_utilities.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common functions for dealing with nodes.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__ARITH_UTILITIES_H
#define CVC4__THEORY__ARITH__ARITH_UTILITIES_H

#include <math.h>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/delta_rational.h"
#include "util/dense_map.h"
#include "util/integer.h"
#include "util/rational.h"

namespace CVC4 {
namespace theory {
namespace arith {

//Sets of Nodes
typedef std::unordered_set<Node, NodeHashFunction> NodeSet;
typedef std::unordered_set<TNode, TNodeHashFunction> TNodeSet;
typedef context::CDHashSet<Node, NodeHashFunction> CDNodeSet;

//Maps from Nodes -> ArithVars, and vice versa
typedef std::unordered_map<Node, ArithVar, NodeHashFunction> NodeToArithVarMap;
typedef DenseMap<Node> ArithVarToNodeMap;

inline Node mkRationalNode(const Rational& q){
  return NodeManager::currentNM()->mkConst<Rational>(q);
}

inline Node mkBoolNode(bool b){
  return NodeManager::currentNM()->mkConst<bool>(b);
}

inline Node mkIntSkolem(const std::string& name){
  return NodeManager::currentNM()->mkSkolem(name, NodeManager::currentNM()->integerType());
}

inline Node mkRealSkolem(const std::string& name){
  return NodeManager::currentNM()->mkSkolem(name, NodeManager::currentNM()->realType());
}

inline Node skolemFunction(const std::string& name, TypeNode dom, TypeNode range){
  NodeManager* currNM = NodeManager::currentNM();
  TypeNode functionType = currNM->mkFunctionType(dom, range);
  return currNM->mkSkolem(name, functionType);
}

/** \f$ k \in {LT, LEQ, EQ, GEQ, GT} \f$ */
inline bool isRelationOperator(Kind k){
  using namespace kind;

  switch(k){
  case LT:
  case LEQ:
  case EQUAL:
  case GEQ:
  case GT:
    return true;
  default:
    return false;
  }
}

/**
 * Given a relational kind, k, return the kind k' s.t.
 * swapping the lefthand and righthand side is equivalent.
 *
 * The following equivalence should hold,
 *   (k l r) <=> (k' r l)
 */
inline Kind reverseRelationKind(Kind k){
  using namespace kind;

  switch(k){
  case LT:    return GT;
  case LEQ:   return GEQ;
  case EQUAL: return EQUAL;
  case GEQ:   return LEQ;
  case GT:    return LT;

  default:
    Unreachable();
  }
}

inline bool evaluateConstantPredicate(Kind k, const Rational& left, const Rational& right){
  using namespace kind;

  switch(k){
  case LT:    return left <  right;
  case LEQ:   return left <= right;
  case EQUAL: return left == right;
  case GEQ:   return left >= right;
  case GT:    return left >  right;
  default:
    Unreachable();
    return true;
  }
}

/**
 * Returns the appropriate coefficient for the infinitesimal given the kind
 * for an arithmetic atom inorder to represent strict inequalities as inequalities.
 *   x < c  becomes  x <= c + (-1) * \f$ \delta \f$
 *   x > c  becomes  x >= x + ( 1) * \f$ \delta \f$
 * Non-strict inequalities have a coefficient of zero.
 */
inline int deltaCoeff(Kind k){
  switch(k){
  case kind::LT:
    return -1;
  case kind::GT:
    return 1;
  default:
    return 0;
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
inline Kind oldSimplifiedKind(TNode literal){
  switch(literal.getKind()){
  case kind::LT:
  case kind::GT:
  case kind::LEQ:
  case kind::GEQ:
  case kind::EQUAL:
    return literal.getKind();
  case  kind::NOT:
    {
      TNode atom = literal[0];
      switch(atom.getKind()){
      case  kind::LEQ: //(not (LEQ x c)) <=> (GT x c)
        return  kind::GT;
      case  kind::GEQ: //(not (GEQ x c)) <=> (LT x c)
        return  kind::LT;
      case  kind::LT: //(not (LT x c)) <=> (GEQ x c)
        return  kind::GEQ;
      case  kind::GT: //(not (GT x c) <=> (LEQ x c)
        return  kind::LEQ;
      case  kind::EQUAL:
        return  kind::DISTINCT;
      default:
        Unreachable();
        return  kind::UNDEFINED_KIND;
      }
    }
  default:
    Unreachable();
    return kind::UNDEFINED_KIND;
  }
}

inline Kind negateKind(Kind k){
  switch(k){
  case kind::LT:       return kind::GEQ;
  case kind::GT:       return kind::LEQ;
  case kind::LEQ:      return kind::GT;
  case kind::GEQ:      return kind::LT;
  case kind::EQUAL:    return kind::DISTINCT;
  case kind::DISTINCT: return kind::EQUAL;
  default:
    return kind::UNDEFINED_KIND;
  }
}

inline Node negateConjunctionAsClause(TNode conjunction){
  Assert(conjunction.getKind() == kind::AND);
  NodeBuilder<> orBuilder(kind::OR);

  for(TNode::iterator i = conjunction.begin(), end=conjunction.end(); i != end; ++i){
    TNode child = *i;
    Node negatedChild = NodeBuilder<1>(kind::NOT)<<(child);
    orBuilder << negatedChild;
  }
  return orBuilder;
}

inline Node maybeUnaryConvert(NodeBuilder<>& builder){
  Assert(builder.getKind() == kind::OR || builder.getKind() == kind::AND
         || builder.getKind() == kind::PLUS || builder.getKind() == kind::MULT);
  Assert(builder.getNumChildren() >= 1);
  if(builder.getNumChildren() == 1){
    return builder[0];
  }else{
    return builder;
  }
}

inline void flattenAnd(Node n, std::vector<TNode>& out){
  Assert(n.getKind() == kind::AND);
  for(Node::iterator i=n.begin(), i_end=n.end(); i != i_end; ++i){
    Node curr = *i;
    if(curr.getKind() == kind::AND){
      flattenAnd(curr, out);
    }else{
      out.push_back(curr);
    }
  }
}

inline Node flattenAnd(Node n){
  std::vector<TNode> out;
  flattenAnd(n, out);
  return NodeManager::currentNM()->mkNode(kind::AND, out);
}

// Returns an node that is the identity of a select few kinds.
inline Node getIdentity(Kind k){
  switch(k){
  case kind::AND:
    return mkBoolNode(true);
  case kind::PLUS:
    return mkRationalNode(0);
  case kind::MULT:
  case kind::NONLINEAR_MULT:
    return mkRationalNode(1);
  default:
    Unreachable();
  }
}

inline Node safeConstructNary(NodeBuilder<>& nb) {
  switch (nb.getNumChildren()) {
    case 0:
      return getIdentity(nb.getKind());
    case 1:
      return nb[0];
    default:
      return (Node)nb;
  }
}

inline Node safeConstructNary(Kind k, const std::vector<Node>& children) {
  switch (children.size()) {
    case 0:
      return getIdentity(k);
    case 1:
      return children[0];
    default:
      return NodeManager::currentNM()->mkNode(k, children);
  }
}

// Returns the multiplication of a and b.
inline Node mkMult(Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::MULT, a, b);
}

// Return a constraint that is equivalent to term being is in the range
// [start, end). This includes start and excludes end.
inline Node mkInRange(Node term, Node start, Node end) {
  NodeManager* nm = NodeManager::currentNM();
  Node above_start = nm->mkNode(kind::LEQ, start, term);
  Node below_end = nm->mkNode(kind::LT, term, end);
  return nm->mkNode(kind::AND, above_start, below_end);
}

// Creates an expression that constrains q to be equal to one of two expressions
// when n is 0 or not. Useful for division by 0 logic.
//   (ite (= n 0) (= q if_zero) (= q not_zero))
inline Node mkOnZeroIte(Node n, Node q, Node if_zero, Node not_zero) {
  Node zero = mkRationalNode(0);
  return n.eqNode(zero).iteNode(q.eqNode(if_zero), q.eqNode(not_zero));
}

inline Node mkPi()
{
  return NodeManager::currentNM()->mkNullaryOperator(
      NodeManager::currentNM()->realType(), kind::PI);
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

/** Arithmetic substitute
 *
 * This computes the substitution n { vars -> subs }, but with the caveat
 * that subterms of n that belong to a theory other than arithmetic are
 * not traversed. In other words, terms that belong to other theories are
 * treated as atomic variables. For example:
 *   (5*f(x) + 7*x ){ x -> 3 } returns 5*f(x) + 7*3.
 */
Node arithSubstitute(Node n, std::vector<Node>& vars, std::vector<Node>& subs);

/** Make the node u >= a ^ a >= l */
Node mkBounded(Node l, Node a, Node u);

Rational leastIntGreaterThan(const Rational&);

Rational greatestIntLessThan(const Rational&);

/** Negates a node in arithmetic proof normal form. */
Node negateProofLiteral(TNode n);

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__ARITH__ARITH_UTILITIES_H */
