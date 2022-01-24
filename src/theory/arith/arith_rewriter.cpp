/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "theory/arith/arith_rewriter.h"

#include <set>
#include <sstream>
#include <stack>
#include <vector>

#include "smt/logic_exception.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/normal_form.h"
#include "theory/arith/operator_elim.h"
#include "theory/theory.h"
#include "util/bitvector.h"
#include "util/divisible.h"
#include "util/iand.h"
#include "util/real_algebraic_number.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arith {

namespace {

template <typename L, typename R>
bool evaluateRelation(Kind rel, const L& l, const R& r)
{
  switch (rel)
  {
    case Kind::LT: return l < r;
    case Kind::LEQ: return l <= r;
    case Kind::EQUAL: return l == r;
    case Kind::GEQ: return l >= r;
    case Kind::GT: return l > r;
    default: Unreachable(); return false;
  }
}

}  // namespace

ArithRewriter::ArithRewriter(OperatorElim& oe) : d_opElim(oe) {}

RewriteResponse ArithRewriter::preRewrite(TNode t)
{
  Trace("arith-rewriter") << "preRewrite(" << t << ")" << std::endl;
  if (isAtom(t))
  {
    auto res = preRewriteAtom(t);
    Trace("arith-rewriter")
        << res.d_status << " -> " << res.d_node << std::endl;
    return res;
  }
  auto res = preRewriteTerm(t);
  Trace("arith-rewriter") << res.d_status << " -> " << res.d_node << std::endl;
  return res;
}

RewriteResponse ArithRewriter::postRewrite(TNode t)
{
  Trace("arith-rewriter") << "postRewrite(" << t << ")" << std::endl;
  if (isAtom(t))
  {
    auto res = postRewriteAtom(t);
    Trace("arith-rewriter")
        << res.d_status << " -> " << res.d_node << std::endl;
    return res;
  }
  auto res = postRewriteTerm(t);
  Trace("arith-rewriter") << res.d_status << " -> " << res.d_node << std::endl;
  return res;
}

RewriteResponse ArithRewriter::preRewriteAtom(TNode atom)
{
  Assert(isAtom(atom));

  NodeManager* nm = NodeManager::currentNM();

  if (isRelationOperator(atom.getKind()) && atom[0] == atom[1])
  {
    switch (atom.getKind())
    {
      case Kind::LT: return RewriteResponse(REWRITE_DONE, nm->mkConst(false));
      case Kind::LEQ: return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
      case Kind::EQUAL: return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
      case Kind::GEQ: return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
      case Kind::GT: return RewriteResponse(REWRITE_DONE, nm->mkConst(false));
      default:;
    }
  }

  switch (atom.getKind())
  {
    case Kind::GT:
      return RewriteResponse(REWRITE_DONE,
                             nm->mkNode(kind::LEQ, atom[0], atom[1]).notNode());
    case Kind::LT:
      return RewriteResponse(REWRITE_DONE,
                             nm->mkNode(kind::GEQ, atom[0], atom[1]).notNode());
    case Kind::IS_INTEGER:
      if (atom[0].getType().isInteger())
      {
        return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
      }
      break;
    case Kind::DIVISIBLE:
      if (atom.getOperator().getConst<Divisible>().k.isOne())
      {
        return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
      }
      break;
    default:;
  }

  return RewriteResponse(REWRITE_DONE, atom);
}

RewriteResponse ArithRewriter::postRewriteAtom(TNode atom)
{
  Assert(isAtom(atom));
  if (atom.getKind() == kind::IS_INTEGER)
  {
    return rewriteExtIntegerOp(atom);
  }
  else if (atom.getKind() == kind::DIVISIBLE)
  {
    if (atom[0].isConst())
    {
      return RewriteResponse(REWRITE_DONE,
                             NodeManager::currentNM()->mkConst(bool(
                                 (atom[0].getConst<Rational>()
                                  / atom.getOperator().getConst<Divisible>().k)
                                     .isIntegral())));
    }
    if (atom.getOperator().getConst<Divisible>().k.isOne())
    {
      return RewriteResponse(REWRITE_DONE,
                             NodeManager::currentNM()->mkConst(true));
    }
    NodeManager* nm = NodeManager::currentNM();
    return RewriteResponse(
        REWRITE_AGAIN,
        nm->mkNode(kind::EQUAL,
                   nm->mkNode(kind::INTS_MODULUS_TOTAL,
                              atom[0],
                              nm->mkConstInt(Rational(
                                  atom.getOperator().getConst<Divisible>().k))),
                   nm->mkConstInt(Rational(0))));
  }

  // left |><| right
  TNode left = atom[0];
  TNode right = atom[1];

  auto* nm = NodeManager::currentNM();
  if (left.isConst())
  {
    const Rational& l = left.getConst<Rational>();
    if (right.isConst())
    {
      const Rational& r = right.getConst<Rational>();
      return RewriteResponse(
          REWRITE_DONE, nm->mkConst(evaluateRelation(atom.getKind(), l, r)));
    }
    else if (right.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
    {
      const RealAlgebraicNumber& r =
          right.getOperator().getConst<RealAlgebraicNumber>();
      return RewriteResponse(
          REWRITE_DONE, nm->mkConst(evaluateRelation(atom.getKind(), l, r)));
    }
  }
  else if (left.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
  {
    const RealAlgebraicNumber& l =
        left.getOperator().getConst<RealAlgebraicNumber>();
    if (right.isConst())
    {
      const Rational& r = right.getConst<Rational>();
      return RewriteResponse(
          REWRITE_DONE, nm->mkConst(evaluateRelation(atom.getKind(), l, r)));
    }
    else if (right.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
    {
      const RealAlgebraicNumber& r =
          right.getOperator().getConst<RealAlgebraicNumber>();
      return RewriteResponse(
          REWRITE_DONE, nm->mkConst(evaluateRelation(atom.getKind(), l, r)));
    }
  }

  Polynomial pleft = Polynomial::parsePolynomial(left);
  Polynomial pright = Polynomial::parsePolynomial(right);

  Debug("arith::rewriter") << "pleft " << pleft.getNode() << std::endl;
  Debug("arith::rewriter") << "pright " << pright.getNode() << std::endl;

  Comparison cmp = Comparison::mkComparison(atom.getKind(), pleft, pright);
  Assert(cmp.isNormalForm());
  return RewriteResponse(REWRITE_DONE, cmp.getNode());
}

bool ArithRewriter::isAtom(TNode n) {
  Kind k = n.getKind();
  return arith::isRelationOperator(k) || k == kind::IS_INTEGER
      || k == kind::DIVISIBLE;
}

RewriteResponse ArithRewriter::rewriteConstant(TNode t){
  Assert(t.isConst());
  Assert(t.getKind() == CONST_RATIONAL || t.getKind() == CONST_INTEGER);

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteRAN(TNode t)
{
  Assert(t.getKind() == REAL_ALGEBRAIC_NUMBER);

  const RealAlgebraicNumber& r =
      t.getOperator().getConst<RealAlgebraicNumber>();
  if (r.isRational())
  {
    return RewriteResponse(
        REWRITE_DONE, NodeManager::currentNM()->mkConstReal(r.toRational()));
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteVariable(TNode t){
  Assert(t.isVar());

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteMinus(TNode t)
{
  Assert(t.getKind() == kind::MINUS);
  Assert(t.getNumChildren() == 2);

  auto* nm = NodeManager::currentNM();

  if (t[0] == t[1])
  {
    return RewriteResponse(REWRITE_DONE,
                           nm->mkConstRealOrInt(t.getType(), Rational(0)));
  }
  return RewriteResponse(
      REWRITE_AGAIN_FULL,
      nm->mkNode(Kind::PLUS, t[0], makeUnaryMinusNode(t[1])));
}

RewriteResponse ArithRewriter::rewriteUMinus(TNode t, bool pre){
  Assert(t.getKind() == kind::UMINUS);

  if (t[0].isConst())
  {
    Rational neg = -(t[0].getConst<Rational>());
    NodeManager* nm = NodeManager::currentNM();
    return RewriteResponse(REWRITE_DONE,
                           nm->mkConstRealOrInt(t[0].getType(), neg));
  }
  if (t[0].getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
  {
    const RealAlgebraicNumber& r =
        t[0].getOperator().getConst<RealAlgebraicNumber>();
    NodeManager* nm = NodeManager::currentNM();
    return RewriteResponse(REWRITE_DONE, nm->mkRealAlgebraicNumber(-r));
  }

  Node noUminus = makeUnaryMinusNode(t[0]);
  if(pre)
    return RewriteResponse(REWRITE_DONE, noUminus);
  else
    return RewriteResponse(REWRITE_AGAIN, noUminus);
}

RewriteResponse ArithRewriter::preRewriteTerm(TNode t){
  if(t.isConst()){
    return rewriteConstant(t);
  }else if(t.isVar()){
    return rewriteVariable(t);
  }else{
    switch(Kind k = t.getKind()){
      case kind::REAL_ALGEBRAIC_NUMBER: return rewriteRAN(t);
      case kind::MINUS: return rewriteMinus(t);
      case kind::UMINUS: return rewriteUMinus(t, true);
      case kind::DIVISION:
      case kind::DIVISION_TOTAL: return rewriteDiv(t, true);
      case kind::PLUS: return preRewritePlus(t);
      case kind::MULT:
      case kind::NONLINEAR_MULT: return preRewriteMult(t);
      case kind::IAND: return RewriteResponse(REWRITE_DONE, t);
      case kind::POW2: return RewriteResponse(REWRITE_DONE, t);
      case kind::EXPONENTIAL:
      case kind::SINE:
      case kind::COSINE:
      case kind::TANGENT:
      case kind::COSECANT:
      case kind::SECANT:
      case kind::COTANGENT:
      case kind::ARCSINE:
      case kind::ARCCOSINE:
      case kind::ARCTANGENT:
      case kind::ARCCOSECANT:
      case kind::ARCSECANT:
      case kind::ARCCOTANGENT:
      case kind::SQRT: return preRewriteTranscendental(t);
      case kind::INTS_DIVISION:
      case kind::INTS_MODULUS: return rewriteIntsDivMod(t, true);
      case kind::INTS_DIVISION_TOTAL:
      case kind::INTS_MODULUS_TOTAL: return rewriteIntsDivModTotal(t, true);
      case kind::ABS: return rewriteAbs(t);
      case kind::IS_INTEGER:
      case kind::TO_INTEGER: return RewriteResponse(REWRITE_DONE, t);
      case kind::TO_REAL:
      case kind::CAST_TO_REAL: return RewriteResponse(REWRITE_DONE, t[0]);
      case kind::POW: return RewriteResponse(REWRITE_DONE, t);
      case kind::PI: return RewriteResponse(REWRITE_DONE, t);
      default: Unhandled() << k;
    }
  }
}

RewriteResponse ArithRewriter::postRewriteTerm(TNode t){
  if(t.isConst()){
    return rewriteConstant(t);
  }else if(t.isVar()){
    return rewriteVariable(t);
  }else{
    Trace("arith-rewriter") << "postRewriteTerm: " << t << std::endl;
    switch(t.getKind()){
      case kind::REAL_ALGEBRAIC_NUMBER: return rewriteRAN(t);
      case kind::MINUS: return rewriteMinus(t);
      case kind::UMINUS: return rewriteUMinus(t, false);
      case kind::DIVISION:
      case kind::DIVISION_TOTAL: return rewriteDiv(t, false);
      case kind::PLUS: return postRewritePlus(t);
      case kind::MULT:
      case kind::NONLINEAR_MULT: return postRewriteMult(t);
      case kind::IAND: return postRewriteIAnd(t);
      case kind::POW2: return postRewritePow2(t);
      case kind::EXPONENTIAL:
      case kind::SINE:
      case kind::COSINE:
      case kind::TANGENT:
      case kind::COSECANT:
      case kind::SECANT:
      case kind::COTANGENT:
      case kind::ARCSINE:
      case kind::ARCCOSINE:
      case kind::ARCTANGENT:
      case kind::ARCCOSECANT:
      case kind::ARCSECANT:
      case kind::ARCCOTANGENT:
      case kind::SQRT: return postRewriteTranscendental(t);
      case kind::INTS_DIVISION:
      case kind::INTS_MODULUS: return rewriteIntsDivMod(t, false);
      case kind::INTS_DIVISION_TOTAL:
      case kind::INTS_MODULUS_TOTAL: return rewriteIntsDivModTotal(t, false);
      case kind::ABS: return rewriteAbs(t);
      case kind::TO_REAL:
      case kind::CAST_TO_REAL: return RewriteResponse(REWRITE_DONE, t[0]);
      case kind::TO_INTEGER: return rewriteExtIntegerOp(t);
      case kind::POW:
      {
        if (t[1].isConst())
        {
          const Rational& exp = t[1].getConst<Rational>();
          TNode base = t[0];
          if(exp.sgn() == 0){
            return RewriteResponse(REWRITE_DONE,
                                   NodeManager::currentNM()->mkConstRealOrInt(
                                       t.getType(), Rational(1)));
          }else if(exp.sgn() > 0 && exp.isIntegral()){
            cvc5::Rational r(expr::NodeValue::MAX_CHILDREN);
            if (exp <= r)
            {
              unsigned num = exp.getNumerator().toUnsignedInt();
              if( num==1 ){
                return RewriteResponse(REWRITE_AGAIN, base);
              }else{
                NodeBuilder nb(kind::MULT);
                for(unsigned i=0; i < num; ++i){
                  nb << base;
                }
                Assert(nb.getNumChildren() > 0);
                Node mult = nb;
                return RewriteResponse(REWRITE_AGAIN, mult);
              }
            }
          }
        }
        else if (t[0].isConst()
                 && t[0].getConst<Rational>().getNumerator().toUnsignedInt()
                        == 2)
        {
          return RewriteResponse(
              REWRITE_DONE, NodeManager::currentNM()->mkNode(kind::POW2, t[1]));
        }

        // Todo improve the exception thrown
        std::stringstream ss;
        ss << "The exponent of the POW(^) operator can only be a positive "
              "integral constant below "
           << (expr::NodeValue::MAX_CHILDREN + 1) << ". ";
        ss << "Exception occurred in:" << std::endl;
        ss << "  " << t;
        throw LogicException(ss.str());
      }
    case kind::PI:
      return RewriteResponse(REWRITE_DONE, t);
    default:
      Unreachable();
    }
  }
}

RewriteResponse ArithRewriter::preRewriteMult(TNode node)
{
  Assert(node.getKind() == kind::MULT
         || node.getKind() == kind::NONLINEAR_MULT);

  for (const auto& child : node)
  {
    if (child.isConst() && child.getConst<Rational>().isZero())
    {
      return RewriteResponse(REWRITE_DONE, child);
    }
  }
  return RewriteResponse(REWRITE_DONE, node);
}

static bool canFlatten(Kind k, TNode t){
  for(TNode::iterator i = t.begin(); i != t.end(); ++i) {
    TNode child = *i;
    if(child.getKind() == k){
      return true;
    }
  }
  return false;
}

static void flatten(std::vector<TNode>& pb, Kind k, TNode t){
  if(t.getKind() == k){
    for(TNode::iterator i = t.begin(); i != t.end(); ++i) {
      TNode child = *i;
      if(child.getKind() == k){
        flatten(pb, k, child);
      }else{
        pb.push_back(child);
      }
    }
  }else{
    pb.push_back(t);
  }
}

static Node flatten(Kind k, TNode t){
  std::vector<TNode> pb;
  flatten(pb, k, t);
  Assert(pb.size() >= 2);
  return NodeManager::currentNM()->mkNode(k, pb);
}

RewriteResponse ArithRewriter::preRewritePlus(TNode t){
  Assert(t.getKind() == kind::PLUS);

  if(canFlatten(kind::PLUS, t)){
    return RewriteResponse(REWRITE_DONE, flatten(kind::PLUS, t));
  }else{
    return RewriteResponse(REWRITE_DONE, t);
  }
}

RewriteResponse ArithRewriter::postRewritePlus(TNode t){
  Assert(t.getKind() == kind::PLUS);
  Assert(t.getNumChildren() > 1);

  Rational rational;
  RealAlgebraicNumber ran;
  std::vector<Monomial> monomials;
  std::vector<Polynomial> polynomials;

  for (const auto& child : t)
  {
    if (child.isConst())
    {
      if (child.getConst<Rational>().isZero())
      {
        continue;
      }
      rational += child.getConst<Rational>();
    }
    else if (child.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
    {
      ran += child.getOperator().getConst<RealAlgebraicNumber>();
    }
    else if (Monomial::isMember(child))
    {
      monomials.emplace_back(Monomial::parseMonomial(child));
    }
    else
    {
      polynomials.emplace_back(Polynomial::parsePolynomial(child));
    }
  }

  if(!monomials.empty()){
    Monomial::sort(monomials);
    Monomial::combineAdjacentMonomials(monomials);
    polynomials.emplace_back(Polynomial::mkPolynomial(monomials));
  }
  if (!rational.isZero())
  {
    polynomials.emplace_back(
        Polynomial::mkPolynomial(Constant::mkConstant(rational)));
  }

  Polynomial poly = Polynomial::sumPolynomials(polynomials);

  if (isZero(ran))
  {
    return RewriteResponse(REWRITE_DONE, poly.getNode());
  }
  if (poly.containsConstant())
  {
    ran += RealAlgebraicNumber(poly.getHead().getConstant().getValue());
    if (!poly.isConstant())
    {
      poly = poly.getTail();
    }
  }

  auto* nm = NodeManager::currentNM();
  if (poly.isConstant())
  {
    return RewriteResponse(REWRITE_DONE, nm->mkRealAlgebraicNumber(ran));
  }
  return RewriteResponse(
      REWRITE_DONE,
      nm->mkNode(Kind::PLUS, nm->mkRealAlgebraicNumber(ran), poly.getNode()));
}

RewriteResponse ArithRewriter::postRewriteMult(TNode t){
  Assert(t.getKind() == kind::MULT || t.getKind() == kind::NONLINEAR_MULT);
  Assert(t.getNumChildren() >= 2);

  Rational rational = Rational(1);
  RealAlgebraicNumber ran = RealAlgebraicNumber(Integer(1));
  Polynomial poly = Polynomial::mkOne();

  for (const auto& child : t)
  {
    if (child.isConst())
    {
      if (child.getConst<Rational>().isZero())
      {
        return RewriteResponse(REWRITE_DONE, child);
      }
      rational *= child.getConst<Rational>();
    }
    else if (child.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
    {
      ran *= child.getOperator().getConst<RealAlgebraicNumber>();
    }
    else
    {
      poly = poly * Polynomial::parsePolynomial(child);
    }
  }

  if (!rational.isOne())
  {
    poly = poly * rational;
  }
  if (isOne(ran))
  {
    return RewriteResponse(REWRITE_DONE, poly.getNode());
  }
  auto* nm = NodeManager::currentNM();
  if (poly.isConstant())
  {
    ran *= RealAlgebraicNumber(poly.getHead().getConstant().getValue());
    return RewriteResponse(REWRITE_DONE, nm->mkRealAlgebraicNumber(ran));
  }
  return RewriteResponse(
      REWRITE_DONE,
      nm->mkNode(
          Kind::MULT, nm->mkRealAlgebraicNumber(ran), poly.getNode()));
}

RewriteResponse ArithRewriter::postRewritePow2(TNode t)
{
  Assert(t.getKind() == kind::POW2);
  NodeManager* nm = NodeManager::currentNM();
  // if constant, we eliminate
  if (t[0].isConst())
  {
    // pow2 is only supported for integers
    Assert(t[0].getType().isInteger());
    Integer i = t[0].getConst<Rational>().getNumerator();
    if (i < 0)
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstInt(Rational(0)));
    }
    // (pow2 t) ---> (pow 2 t) and continue rewriting to eliminate pow
    Node two = nm->mkConstInt(Rational(Integer(2)));
    Node ret = nm->mkNode(kind::POW, two, t[0]);
    return RewriteResponse(REWRITE_AGAIN, ret);
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteIAnd(TNode t)
{
  Assert(t.getKind() == kind::IAND);
  size_t bsize = t.getOperator().getConst<IntAnd>().d_size;
  NodeManager* nm = NodeManager::currentNM();
  // if constant, we eliminate
  if (t[0].isConst() && t[1].isConst())
  {
    Node iToBvop = nm->mkConst(IntToBitVector(bsize));
    Node arg1 = nm->mkNode(kind::INT_TO_BITVECTOR, iToBvop, t[0]);
    Node arg2 = nm->mkNode(kind::INT_TO_BITVECTOR, iToBvop, t[1]);
    Node bvand = nm->mkNode(kind::BITVECTOR_AND, arg1, arg2);
    Node ret = nm->mkNode(kind::BITVECTOR_TO_NAT, bvand);
    return RewriteResponse(REWRITE_AGAIN_FULL, ret);
  }
  else if (t[0] > t[1])
  {
    // ((_ iand k) x y) ---> ((_ iand k) y x) if x > y by node ordering
    Node ret = nm->mkNode(kind::IAND, t.getOperator(), t[1], t[0]);
    return RewriteResponse(REWRITE_AGAIN, ret);
  }
  else if (t[0] == t[1])
  {
    // ((_ iand k) x x) ---> x
    return RewriteResponse(REWRITE_DONE, t[0]);
  }
  // simplifications involving constants
  for (unsigned i = 0; i < 2; i++)
  {
    if (!t[i].isConst())
    {
      continue;
    }
    if (t[i].getConst<Rational>().sgn() == 0)
    {
      // ((_ iand k) 0 y) ---> 0
      return RewriteResponse(REWRITE_DONE, t[i]);
    }
    if (t[i].getConst<Rational>().getNumerator() == Integer(2).pow(bsize) - 1)
    {
      // ((_ iand k) 111...1 y) ---> y
      return RewriteResponse(REWRITE_DONE, t[i == 0 ? 1 : 0]);
    }
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::preRewriteTranscendental(TNode t) {
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteTranscendental(TNode t) { 
  Trace("arith-tf-rewrite") << "Rewrite transcendental function : " << t << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  switch( t.getKind() ){
  case kind::EXPONENTIAL: {
    if (t[0].isConst())
    {
      Node one = nm->mkConstReal(Rational(1));
      if(t[0].getConst<Rational>().sgn()>=0 && t[0].getType().isInteger() && t[0]!=one){
        return RewriteResponse(
            REWRITE_AGAIN,
            nm->mkNode(kind::POW, nm->mkNode(kind::EXPONENTIAL, one), t[0]));
      }else{          
        return RewriteResponse(REWRITE_DONE, t);
      }
    }
    else if (t[0].getKind() == kind::PLUS)
    {
      std::vector<Node> product;
      for (const Node tc : t[0])
      {
        product.push_back(nm->mkNode(kind::EXPONENTIAL, tc));
      }
      // We need to do a full rewrite here, since we can get exponentials of
      // constants, e.g. when we are rewriting exp(2 + x)
      return RewriteResponse(REWRITE_AGAIN_FULL,
                             nm->mkNode(kind::MULT, product));
    }
  }
    break;
  case kind::SINE:
    if (t[0].isConst())
    {
      const Rational& rat = t[0].getConst<Rational>();
      if(rat.sgn() == 0){
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(Rational(0)));
      }
      else if (rat.sgn() == -1)
      {
        Node ret = nm->mkNode(kind::UMINUS,
                              nm->mkNode(kind::SINE, nm->mkConstReal(-rat)));
        return RewriteResponse(REWRITE_AGAIN_FULL, ret);
      }
    }else{
      // get the factor of PI in the argument
      Node pi_factor;
      Node pi;
      Node rem;
      std::map<Node, Node> msum;
      if (ArithMSum::getMonomialSum(t[0], msum))
      {
        pi = mkPi();
        std::map<Node, Node>::iterator itm = msum.find(pi);
        if (itm != msum.end())
        {
          if (itm->second.isNull())
          {
            pi_factor = nm->mkConstReal(Rational(1));
          }
          else
          {
            pi_factor = itm->second;
          }
          msum.erase(pi);
          if (!msum.empty())
          {
            rem = ArithMSum::mkNode(t[0].getType(), msum);
          }
        }
      }
      else
      {
        Assert(false);
      }

      // if there is a factor of PI
      if( !pi_factor.isNull() ){
        Trace("arith-tf-rewrite-debug") << "Process pi factor = " << pi_factor << std::endl;
        Rational r = pi_factor.getConst<Rational>();
        Rational r_abs = r.abs();
        Rational rone = Rational(1);
        Node ntwo = nm->mkConstInt(Rational(2));
        if (r_abs > rone)
        {
          //add/substract 2*pi beyond scope
          Node ra_div_two = nm->mkNode(
              kind::INTS_DIVISION, mkRationalNode(r_abs + rone), ntwo);
          Node new_pi_factor;
          if( r.sgn()==1 ){
            new_pi_factor =
                nm->mkNode(kind::MINUS,
                           pi_factor,
                           nm->mkNode(kind::MULT, ntwo, ra_div_two));
          }else{
            Assert(r.sgn() == -1);
            new_pi_factor =
                nm->mkNode(kind::PLUS,
                           pi_factor,
                           nm->mkNode(kind::MULT, ntwo, ra_div_two));
          }
          Node new_arg = nm->mkNode(kind::MULT, new_pi_factor, pi);
          if (!rem.isNull())
          {
            new_arg = nm->mkNode(kind::PLUS, new_arg, rem);
          }
          // sin( 2*n*PI + x ) = sin( x )
          return RewriteResponse(REWRITE_AGAIN_FULL,
                                 nm->mkNode(kind::SINE, new_arg));
        }
        else if (r_abs == rone)
        {
          // sin( PI + x ) = -sin( x )
          if (rem.isNull())
          {
            return RewriteResponse(REWRITE_DONE, nm->mkConstReal(Rational(0)));
          }
          else
          {
            return RewriteResponse(
                REWRITE_AGAIN_FULL,
                nm->mkNode(kind::UMINUS, nm->mkNode(kind::SINE, rem)));
          }
        }
        else if (rem.isNull())
        {
          // other rational cases based on Niven's theorem
          // (https://en.wikipedia.org/wiki/Niven%27s_theorem)
          Integer one = Integer(1);
          Integer two = Integer(2);
          Integer six = Integer(6);
          if (r_abs.getDenominator() == two)
          {
            Assert(r_abs.getNumerator() == one);
            return RewriteResponse(REWRITE_DONE,
                                   nm->mkConstReal(Rational(r.sgn())));
          }
          else if (r_abs.getDenominator() == six)
          {
            Integer five = Integer(5);
            if (r_abs.getNumerator() == one || r_abs.getNumerator() == five)
            {
              return RewriteResponse(
                  REWRITE_DONE,
                  nm->mkConstReal(Rational(r.sgn()) / Rational(2)));
            }
          }
        }
      }
    }
    break;
  case kind::COSINE: {
    return RewriteResponse(
        REWRITE_AGAIN_FULL,
        nm->mkNode(
            kind::SINE,
            nm->mkNode(kind::MINUS,
                       nm->mkNode(kind::MULT,
                                  nm->mkConstReal(Rational(1) / Rational(2)),
                                  mkPi()),
                       t[0])));
  }
  break;
  case kind::TANGENT:
  {
    return RewriteResponse(REWRITE_AGAIN_FULL,
                           nm->mkNode(kind::DIVISION,
                                      nm->mkNode(kind::SINE, t[0]),
                                      nm->mkNode(kind::COSINE, t[0])));
  }
  break;
  case kind::COSECANT:
  {
    return RewriteResponse(REWRITE_AGAIN_FULL,
                           nm->mkNode(kind::DIVISION,
                                      nm->mkConstReal(Rational(1)),
                                      nm->mkNode(kind::SINE, t[0])));
  }
  break;
  case kind::SECANT:
  {
    return RewriteResponse(REWRITE_AGAIN_FULL,
                           nm->mkNode(kind::DIVISION,
                                      nm->mkConstReal(Rational(1)),
                                      nm->mkNode(kind::COSINE, t[0])));
  }
  break;
  case kind::COTANGENT:
  {
    return RewriteResponse(REWRITE_AGAIN_FULL,
                           nm->mkNode(kind::DIVISION,
                                      nm->mkNode(kind::COSINE, t[0]),
                                      nm->mkNode(kind::SINE, t[0])));
  }
  break;
  default:
    break;
  }
  return RewriteResponse(REWRITE_DONE, t);
}

Node ArithRewriter::makeUnaryMinusNode(TNode n){
  NodeManager* nm = NodeManager::currentNM();
  Rational qNegOne(-1);
  return nm->mkNode(kind::MULT, nm->mkConstRealOrInt(n.getType(), qNegOne), n);
}

RewriteResponse ArithRewriter::rewriteDiv(TNode t, bool pre){
  Assert(t.getKind() == kind::DIVISION_TOTAL || t.getKind() == kind::DIVISION);
  Assert(t.getNumChildren() == 2);

  Node left = t[0];
  Node right = t[1];
  if (right.isConst())
  {
    NodeManager* nm = NodeManager::currentNM();
    const Rational& den = right.getConst<Rational>();

    if(den.isZero()){
      if(t.getKind() == kind::DIVISION_TOTAL){
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(0));
      }else{
        // This is unsupported, but this is not a good place to complain
        return RewriteResponse(REWRITE_DONE, t);
      }
    }
    Assert(den != Rational(0));

    if (left.isConst())
    {
      const Rational& num = left.getConst<Rational>();
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(num / den));
    }
    if (left.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
    {
      const RealAlgebraicNumber& num =
          left.getOperator().getConst<RealAlgebraicNumber>();
      return RewriteResponse(
          REWRITE_DONE,
          nm->mkRealAlgebraicNumber(num / RealAlgebraicNumber(den)));
    }

    Node result = nm->mkConstReal(den.inverse());
    Node mult = NodeManager::currentNM()->mkNode(kind::MULT, left, result);
    if (pre)
    {
      return RewriteResponse(REWRITE_DONE, mult);
    }
    else
    {
      return RewriteResponse(REWRITE_AGAIN, mult);
    }
  }
  if (right.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
  {
    NodeManager* nm = NodeManager::currentNM();
    const RealAlgebraicNumber& den =
        right.getOperator().getConst<RealAlgebraicNumber>();
    if (left.isConst())
    {
      const Rational& num = left.getConst<Rational>();
      return RewriteResponse(
          REWRITE_DONE,
          nm->mkRealAlgebraicNumber(RealAlgebraicNumber(num) / den));
    }
    if (left.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
    {
      const RealAlgebraicNumber& num =
          left.getOperator().getConst<RealAlgebraicNumber>();
      return RewriteResponse(REWRITE_DONE,
                             nm->mkRealAlgebraicNumber(num / den));
    }

    Node result = nm->mkRealAlgebraicNumber(inverse(den));
    Node mult = NodeManager::currentNM()->mkNode(kind::MULT,left,result);
    if(pre){
      return RewriteResponse(REWRITE_DONE, mult);
    }else{
      return RewriteResponse(REWRITE_AGAIN, mult);
    }
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteAbs(TNode t)
{
  Assert(t.getKind() == Kind::ABS);
  Assert(t.getNumChildren() == 1);

  if (t[0].isConst())
  {
    const Rational& rat = t[0].getConst<Rational>();
    if (rat >= 0)
    {
      return RewriteResponse(REWRITE_DONE, t[0]);
    }
    return RewriteResponse(
        REWRITE_DONE,
        NodeManager::currentNM()->mkConstRealOrInt(t[0].getType(), -rat));
  }
  if (t[0].getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
  {
    const RealAlgebraicNumber& ran =
        t[0].getOperator().getConst<RealAlgebraicNumber>();
    if (ran >= RealAlgebraicNumber())
    {
      return RewriteResponse(REWRITE_DONE, t[0]);
    }
    return RewriteResponse(
        REWRITE_DONE, NodeManager::currentNM()->mkRealAlgebraicNumber(-ran));
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteIntsDivMod(TNode t, bool pre)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = t.getKind();
  if (k == kind::INTS_MODULUS)
  {
    if (t[1].isConst() && !t[1].getConst<Rational>().isZero())
    {
      // can immediately replace by INTS_MODULUS_TOTAL
      Node ret = nm->mkNode(kind::INTS_MODULUS_TOTAL, t[0], t[1]);
      return returnRewrite(t, ret, Rewrite::MOD_TOTAL_BY_CONST);
    }
  }
  if (k == kind::INTS_DIVISION)
  {
    if (t[1].isConst() && !t[1].getConst<Rational>().isZero())
    {
      // can immediately replace by INTS_DIVISION_TOTAL
      Node ret = nm->mkNode(kind::INTS_DIVISION_TOTAL, t[0], t[1]);
      return returnRewrite(t, ret, Rewrite::DIV_TOTAL_BY_CONST);
    }
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteExtIntegerOp(TNode t)
{
  Assert(t.getKind() == kind::TO_INTEGER || t.getKind() == kind::IS_INTEGER);
  bool isPred = t.getKind() == kind::IS_INTEGER;
  NodeManager* nm = NodeManager::currentNM();
  if (t[0].isConst())
  {
    Node ret;
    if (isPred)
    {
      ret = nm->mkConst(t[0].getConst<Rational>().isIntegral());
    }
    else
    {
      ret = nm->mkConstInt(Rational(t[0].getConst<Rational>().floor()));
    }
    return returnRewrite(t, ret, Rewrite::INT_EXT_CONST);
  }
  if (t[0].getType().isInteger())
  {
    Node ret = isPred ? nm->mkConst(true) : Node(t[0]);
    return returnRewrite(t, ret, Rewrite::INT_EXT_INT);
  }
  if (t[0].getKind() == kind::PI)
  {
    Node ret = isPred ? nm->mkConst(false) : nm->mkConstReal(Rational(3));
    return returnRewrite(t, ret, Rewrite::INT_EXT_PI);
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteIntsDivModTotal(TNode t, bool pre)
{
  if (pre)
  {
    // do not rewrite at prewrite.
    return RewriteResponse(REWRITE_DONE, t);
  }
  NodeManager* nm = NodeManager::currentNM();
  Kind k = t.getKind();
  Assert(k == kind::INTS_MODULUS_TOTAL || k == kind::INTS_DIVISION_TOTAL);
  TNode n = t[0];
  TNode d = t[1];
  bool dIsConstant = d.isConst();
  if(dIsConstant && d.getConst<Rational>().isZero()){
    // (div x 0) ---> 0 or (mod x 0) ---> 0
    return returnRewrite(t, nm->mkConstInt(0), Rewrite::DIV_MOD_BY_ZERO);
  }else if(dIsConstant && d.getConst<Rational>().isOne()){
    if (k == kind::INTS_MODULUS_TOTAL)
    {
      // (mod x 1) --> 0
      return returnRewrite(t, nm->mkConstInt(0), Rewrite::MOD_BY_ONE);
    }
    Assert(k == kind::INTS_DIVISION_TOTAL);
    // (div x 1) --> x
    return returnRewrite(t, n, Rewrite::DIV_BY_ONE);
  }
  else if (dIsConstant && d.getConst<Rational>().sgn() < 0)
  {
    // pull negation
    // (div x (- c)) ---> (- (div x c))
    // (mod x (- c)) ---> (mod x c)
    Node nn = nm->mkNode(k, t[0], nm->mkConstInt(-t[1].getConst<Rational>()));
    Node ret = (k == kind::INTS_DIVISION || k == kind::INTS_DIVISION_TOTAL)
                   ? nm->mkNode(kind::UMINUS, nn)
                   : nn;
    return returnRewrite(t, ret, Rewrite::DIV_MOD_PULL_NEG_DEN);
  }
  else if (dIsConstant && n.isConst())
  {
    Assert(d.getConst<Rational>().isIntegral());
    Assert(n.getConst<Rational>().isIntegral());
    Assert(!d.getConst<Rational>().isZero());
    Integer di = d.getConst<Rational>().getNumerator();
    Integer ni = n.getConst<Rational>().getNumerator();

    bool isDiv = (k == kind::INTS_DIVISION || k == kind::INTS_DIVISION_TOTAL);

    Integer result = isDiv ? ni.euclidianDivideQuotient(di) : ni.euclidianDivideRemainder(di);

    // constant evaluation
    // (mod c1 c2) ---> c3 or (div c1 c2) ---> c3
    Node resultNode = nm->mkConstInt(Rational(result));
    return returnRewrite(t, resultNode, Rewrite::CONST_EVAL);
  }
  if (k == kind::INTS_MODULUS_TOTAL)
  {
    // Note these rewrites do not need to account for modulus by zero as being
    // a UF, which is handled by the reduction of INTS_MODULUS.
    Kind k0 = t[0].getKind();
    if (k0 == kind::INTS_MODULUS_TOTAL && t[0][1] == t[1])
    {
      // (mod (mod x c) c) --> (mod x c)
      return returnRewrite(t, t[0], Rewrite::MOD_OVER_MOD);
    }
    else if (k0 == kind::NONLINEAR_MULT || k0 == kind::MULT || k0 == kind::PLUS)
    {
      // can drop all
      std::vector<Node> newChildren;
      bool childChanged = false;
      for (const Node& tc : t[0])
      {
        if (tc.getKind() == kind::INTS_MODULUS_TOTAL && tc[1] == t[1])
        {
          newChildren.push_back(tc[0]);
          childChanged = true;
          continue;
        }
        newChildren.push_back(tc);
      }
      if (childChanged)
      {
        // (mod (op ... (mod x c) ...) c) ---> (mod (op ... x ...) c) where
        // op is one of { NONLINEAR_MULT, MULT, PLUS }.
        Node ret = nm->mkNode(k0, newChildren);
        ret = nm->mkNode(kind::INTS_MODULUS_TOTAL, ret, t[1]);
        return returnRewrite(t, ret, Rewrite::MOD_CHILD_MOD);
      }
    }
  }
  else
  {
    Assert(k == kind::INTS_DIVISION_TOTAL);
    // Note these rewrites do not need to account for division by zero as being
    // a UF, which is handled by the reduction of INTS_DIVISION.
    if (t[0].getKind() == kind::INTS_MODULUS_TOTAL && t[0][1] == t[1])
    {
      // (div (mod x c) c) --> 0
      Node ret = nm->mkConstInt(0);
      return returnRewrite(t, ret, Rewrite::DIV_OVER_MOD);
    }
  }
  return RewriteResponse(REWRITE_DONE, t);
}

TrustNode ArithRewriter::expandDefinition(Node node)
{
  // call eliminate operators, to eliminate partial operators only
  std::vector<SkolemLemma> lems;
  TrustNode ret = d_opElim.eliminate(node, lems, true);
  Assert(lems.empty());
  return ret;
}

RewriteResponse ArithRewriter::returnRewrite(TNode t, Node ret, Rewrite r)
{
  Trace("arith-rewrite") << "ArithRewriter : " << t << " == " << ret << " by "
                         << r << std::endl;
  return RewriteResponse(REWRITE_AGAIN_FULL, ret);
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
