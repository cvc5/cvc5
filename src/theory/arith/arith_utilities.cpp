/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Alex Ozdemir, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of common functions for dealing with nodes.
 */

#include "theory/arith/arith_utilities.h"

#include <cmath>

#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {

Kind joinKinds(Kind k1, Kind k2)
{
  if (k2 < k1)
  {
    return joinKinds(k2, k1);
  }
  else if (k1 == k2)
  {
    return k1;
  }
  Assert(isRelationOperator(k1));
  Assert(isRelationOperator(k2));
  if (k1 == EQUAL)
  {
    if (k2 == LEQ || k2 == GEQ)
    {
      return k1;
    }
  }
  else if (k1 == LT)
  {
    if (k2 == LEQ)
    {
      return k1;
    }
  }
  else if (k1 == LEQ)
  {
    if (k2 == GEQ)
    {
      return EQUAL;
    }
  }
  else if (k1 == GT)
  {
    if (k2 == GEQ)
    {
      return k1;
    }
  }
  return UNDEFINED_KIND;
}

Kind transKinds(Kind k1, Kind k2)
{
  if (k2 < k1)
  {
    return transKinds(k2, k1);
  }
  else if (k1 == k2)
  {
    return k1;
  }
  Assert(isRelationOperator(k1));
  Assert(isRelationOperator(k2));
  if (k1 == EQUAL)
  {
    return k2;
  }
  else if (k1 == LT)
  {
    if (k2 == LEQ)
    {
      return k1;
    }
  }
  else if (k1 == GT)
  {
    if (k2 == GEQ)
    {
      return k1;
    }
  }
  return UNDEFINED_KIND;
}

Node mkZero(const TypeNode& tn)
{
  return NodeManager::currentNM()->mkConstRealOrInt(tn, 0);
}

bool isZero(const Node& n)
{
  Assert(n.getType().isRealOrInt());
  return n.isConst() && n.getConst<Rational>().sgn() == 0;
}

Node mkOne(const TypeNode& tn, bool isNeg)
{
  return NodeManager::currentNM()->mkConstRealOrInt(tn, isNeg ? -1 : 1);
}

bool isTranscendentalKind(Kind k)
{
  // many operators are eliminated during rewriting
  Assert(k != TANGENT && k != COSINE && k != COSECANT
         && k != SECANT && k != COTANGENT);
  return k == EXPONENTIAL || k == SINE || k == PI;
}

Node getApproximateConstant(Node c, bool isLower, unsigned prec)
{
  if (!c.isConst())
  {
    Assert(false) << "getApproximateConstant: non-constant input " << c;
    return Node::null();
  }
  Rational cr = c.getConst<Rational>();

  unsigned lower = 0;
  unsigned upper = std::pow(10, prec);

  Rational den = Rational(upper);
  if (cr.getDenominator() < den.getNumerator())
  {
    // denominator is not more than precision, we return it
    return c;
  }

  int csign = cr.sgn();
  Assert(csign != 0);
  if (csign == -1)
  {
    cr = -cr;
  }
  Rational one = Rational(1);
  Rational ten = Rational(10);
  Rational pow_ten = Rational(1);
  // inefficient for large numbers
  while (cr >= one)
  {
    cr = cr / ten;
    pow_ten = pow_ten * ten;
  }
  Rational allow_err = one / den;

  // now do binary search
  Rational two = Rational(2);
  NodeManager* nm = NodeManager::currentNM();
  Node cret;
  do
  {
    unsigned curr = (lower + upper) / 2;
    Rational curr_r = Rational(curr) / den;
    Rational err = cr - curr_r;
    int esign = err.sgn();
    if (err.abs() <= allow_err)
    {
      if (esign == 1 && !isLower)
      {
        curr_r = Rational(curr + 1) / den;
      }
      else if (esign == -1 && isLower)
      {
        curr_r = Rational(curr - 1) / den;
      }
      curr_r = curr_r * pow_ten;
      cret = nm->mkConst(CONST_RATIONAL, csign == 1 ? curr_r : -curr_r);
    }
    else
    {
      Assert(esign != 0);
      // update lower/upper
      if (esign == -1)
      {
        upper = curr;
      }
      else if (esign == 1)
      {
        lower = curr;
      }
    }
  } while (cret.isNull());
  return cret;
}

void printRationalApprox(const char* c, Node cr, unsigned prec)
{
  if (!cr.isConst())
  {
    Assert(false) << "printRationalApprox: non-constant input " << cr;
    Trace(c) << cr;
    return;
  }
  Node ca = getApproximateConstant(cr, true, prec);
  if (ca != cr)
  {
    Trace(c) << "(+ ";
  }
  Trace(c) << ca;
  if (ca != cr)
  {
    Trace(c) << " [0,10^" << prec << "])";
  }
}

Node mkBounded(Node l, Node a, Node u)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(AND, nm->mkNode(GEQ, a, l), nm->mkNode(LEQ, a, u));
}

Rational leastIntGreaterThan(const Rational& q) { return q.floor() + 1; }

Rational greatestIntLessThan(const Rational& q) { return q.ceiling() - 1; }

Node negateProofLiteral(TNode n)
{
  auto nm = NodeManager::currentNM();
  switch (n.getKind())
  {
    case Kind::GT:
    {
      return nm->mkNode(Kind::LEQ, n[0], n[1]);
    }
    case Kind::LT:
    {
      return nm->mkNode(Kind::GEQ, n[0], n[1]);
    }
    case Kind::LEQ:
    {
      return nm->mkNode(Kind::GT, n[0], n[1]);
    }
    case Kind::GEQ:
    {
      return nm->mkNode(Kind::LT, n[0], n[1]);
    }
    case Kind::EQUAL:
    case Kind::NOT:
    {
      return n.negate();
    }
    default: Unhandled() << n;
  }
}

Node multConstants(const Node& c1, const Node& c2)
{
  Assert(!c1.isNull() && c1.isConst());
  Assert(!c2.isNull() && c2.isConst());
  NodeManager* nm = NodeManager::currentNM();
  // real type if either has type real
  TypeNode tn = c1.getType();
  if (tn.isInteger())
  {
    tn = c2.getType();
  }
  Assert(tn.isRealOrInt());
  return nm->mkConstRealOrInt(
      tn, Rational(c1.getConst<Rational>() * c2.getConst<Rational>()));
}

Node mkEquality(const Node& a, const Node& b)
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(a.getType().isRealOrInt());
  Assert(b.getType().isRealOrInt());
  // if they have the same type, just make them equal
  if (a.getType() == b.getType())
  {
    return nm->mkNode(EQUAL, a, b);
  }
  // otherwise subtract and set equal to zero
  Node diff = nm->mkNode(Kind::SUB, a, b);
  return nm->mkNode(EQUAL, diff, mkZero(diff.getType()));
}

std::pair<Node,Node> mkSameType(const Node& a, const Node& b)
{
  TypeNode at = a.getType();
  TypeNode bt = b.getType();
  if (at == bt)
  {
    return {a, b};
  }
  NodeManager* nm = NodeManager::currentNM();
  if (at.isInteger() && bt.isReal())
  {
    return {nm->mkNode(kind::TO_REAL, a), b};
  }
  Assert(at.isReal() && bt.isInteger());
  return {a, nm->mkNode(kind::TO_REAL, b)};
}

/* ------------------------------------------------------------------------- */

Node eliminateBv2Nat(TNode node)
{
  const unsigned size = bv::utils::getSize(node[0]);
  NodeManager* const nm = NodeManager::currentNM();
  const Node z = nm->mkConstInt(Rational(0));
  const Node bvone = bv::utils::mkOne(1);

  Integer i = 1;
  std::vector<Node> children;
  for (unsigned bit = 0; bit < size; ++bit, i *= 2)
  {
    Node cond =
        nm->mkNode(kind::EQUAL,
                   nm->mkNode(nm->mkConst(BitVectorExtract(bit, bit)), node[0]),
                   bvone);
    children.push_back(
        nm->mkNode(kind::ITE, cond, nm->mkConstInt(Rational(i)), z));
  }
  // avoid plus with one child
  return children.size() == 1 ? children[0] : nm->mkNode(kind::ADD, children);
}

Node eliminateInt2Bv(TNode node)
{
  const uint32_t size = node.getOperator().getConst<IntToBitVector>().d_size;
  NodeManager* const nm = NodeManager::currentNM();
  const Node bvzero = bv::utils::mkZero(1);
  const Node bvone = bv::utils::mkOne(1);

  std::vector<Node> v;
  Integer i = 2;
  while (v.size() < size)
  {
    Node cond = nm->mkNode(
        kind::GEQ,
        nm->mkNode(
            kind::INTS_MODULUS_TOTAL, node[0], nm->mkConstInt(Rational(i))),
        nm->mkConstInt(Rational(i, 2)));
    v.push_back(nm->mkNode(kind::ITE, cond, bvone, bvzero));
    i *= 2;
  }
  if (v.size() == 1)
  {
    return v[0];
  }
  NodeBuilder result(kind::BITVECTOR_CONCAT);
  result.append(v.rbegin(), v.rend());
  return Node(result);
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
