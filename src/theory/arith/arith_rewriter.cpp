/*********************                                                        */
/*! \file arith_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include <set>
#include <stack>
#include <vector>

#include "smt/logic_exception.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/normal_form.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace arith {

bool ArithRewriter::isAtom(TNode n) {
  Kind k = n.getKind();
  return arith::isRelationOperator(k) || k == kind::IS_INTEGER
      || k == kind::DIVISIBLE;
}

RewriteResponse ArithRewriter::rewriteConstant(TNode t){
  Assert(t.isConst());
  Assert(t.getKind() == kind::CONST_RATIONAL);

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteVariable(TNode t){
  Assert(t.isVar());

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteMinus(TNode t, bool pre){
  Assert(t.getKind()== kind::MINUS);

  if(pre){
    if(t[0] == t[1]){
      Rational zero(0);
      Node zeroNode  = mkRationalNode(zero);
      return RewriteResponse(REWRITE_DONE, zeroNode);
    }else{
      Node noMinus = makeSubtractionNode(t[0],t[1]);
      return RewriteResponse(REWRITE_DONE, noMinus);
    }
  }else{
    Polynomial minuend = Polynomial::parsePolynomial(t[0]);
    Polynomial subtrahend = Polynomial::parsePolynomial(t[1]);
    Polynomial diff = minuend - subtrahend;
    return RewriteResponse(REWRITE_DONE, diff.getNode());
  }
}

RewriteResponse ArithRewriter::rewriteUMinus(TNode t, bool pre){
  Assert(t.getKind()== kind::UMINUS);

  if(t[0].getKind() == kind::CONST_RATIONAL){
    Rational neg = -(t[0].getConst<Rational>());
    return RewriteResponse(REWRITE_DONE, mkRationalNode(neg));
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
    case kind::MINUS:
      return rewriteMinus(t, true);
    case kind::UMINUS:
      return rewriteUMinus(t, true);
    case kind::DIVISION:
    case kind::DIVISION_TOTAL:
      return rewriteDiv(t,true);
    case kind::PLUS:
      return preRewritePlus(t);
    case kind::MULT:
    case kind::NONLINEAR_MULT:
      return preRewriteMult(t);  
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
    case kind::INTS_MODULUS:
      return RewriteResponse(REWRITE_DONE, t);
    case kind::INTS_DIVISION_TOTAL:
    case kind::INTS_MODULUS_TOTAL:
      return rewriteIntsDivModTotal(t,true);
    case kind::ABS:
      if(t[0].isConst()) {
        const Rational& rat = t[0].getConst<Rational>();
        if(rat >= 0) {
          return RewriteResponse(REWRITE_DONE, t[0]);
        } else {
          return RewriteResponse(REWRITE_DONE,
                                 NodeManager::currentNM()->mkConst(-rat));
        }
      }
      return RewriteResponse(REWRITE_DONE, t);
    case kind::IS_INTEGER:
    case kind::TO_INTEGER:
      return RewriteResponse(REWRITE_DONE, t);
    case kind::TO_REAL:
      return RewriteResponse(REWRITE_DONE, t[0]);
    case kind::POW:
      return RewriteResponse(REWRITE_DONE, t);
    case kind::PI:
      return RewriteResponse(REWRITE_DONE, t);
    default:
      Unhandled(k);
    }
  }
}

RewriteResponse ArithRewriter::postRewriteTerm(TNode t){
  if(t.isConst()){
    return rewriteConstant(t);
  }else if(t.isVar()){
    return rewriteVariable(t);
  }else{
    switch(t.getKind()){
    case kind::MINUS:
      return rewriteMinus(t, false);
    case kind::UMINUS:
      return rewriteUMinus(t, false);
    case kind::DIVISION:
    case kind::DIVISION_TOTAL:
      return rewriteDiv(t, false);
    case kind::PLUS:
      return postRewritePlus(t);
    case kind::MULT:
    case kind::NONLINEAR_MULT:
      return postRewriteMult(t);    
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
    case kind::INTS_MODULUS:
      return RewriteResponse(REWRITE_DONE, t);
    case kind::INTS_DIVISION_TOTAL:
    case kind::INTS_MODULUS_TOTAL:
      return rewriteIntsDivModTotal(t, false);
    case kind::ABS:
      if(t[0].isConst()) {
        const Rational& rat = t[0].getConst<Rational>();
        if(rat >= 0) {
          return RewriteResponse(REWRITE_DONE, t[0]);
        } else {
          return RewriteResponse(REWRITE_DONE,
                                 NodeManager::currentNM()->mkConst(-rat));
        }
      }
    case kind::TO_REAL:
      return RewriteResponse(REWRITE_DONE, t[0]);
    case kind::TO_INTEGER:
      if(t[0].isConst()) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(Rational(t[0].getConst<Rational>().floor())));
      }
      if(t[0].getType().isInteger()) {
        return RewriteResponse(REWRITE_DONE, t[0]);
      }
      //Unimplemented("TO_INTEGER, nonconstant");
      //return rewriteToInteger(t);
      return RewriteResponse(REWRITE_DONE, t);
    case kind::IS_INTEGER:
      if(t[0].isConst()) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(t[0].getConst<Rational>().getDenominator() == 1));
      }
      if(t[0].getType().isInteger()) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      }
      //Unimplemented("IS_INTEGER, nonconstant");
      //return rewriteIsInteger(t);
      return RewriteResponse(REWRITE_DONE, t);
    case kind::POW:
      {
        if(t[1].getKind() == kind::CONST_RATIONAL){
          const Rational& exp = t[1].getConst<Rational>();
          TNode base = t[0];
          if(exp.sgn() == 0){
            return RewriteResponse(REWRITE_DONE, mkRationalNode(Rational(1)));
          }else if(exp.sgn() > 0 && exp.isIntegral()){
            CVC4::Rational r(INT_MAX);
            if( exp<r ){
              unsigned num = exp.getNumerator().toUnsignedInt();
              if( num==1 ){
                return RewriteResponse(REWRITE_AGAIN, base);
              }else{
                NodeBuilder<> nb(kind::MULT);
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

        // Todo improve the exception thrown
        std::stringstream ss;
        ss << "The POW(^) operator can only be used with a natural number ";
        ss << "in the exponent.  Exception occurred in:" << std::endl;
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


RewriteResponse ArithRewriter::preRewriteMult(TNode t){
  Assert(t.getKind()== kind::MULT || t.getKind()== kind::NONLINEAR_MULT);

  if(t.getNumChildren() == 2){
    if(t[0].getKind() == kind::CONST_RATIONAL
       && t[0].getConst<Rational>().isOne()){
      return RewriteResponse(REWRITE_DONE, t[1]);
    }
    if(t[1].getKind() == kind::CONST_RATIONAL
       && t[1].getConst<Rational>().isOne()){
      return RewriteResponse(REWRITE_DONE, t[0]);
    }
  }

  // Rewrite multiplications with a 0 argument and to 0
  for(TNode::iterator i = t.begin(); i != t.end(); ++i) {
    if((*i).getKind() == kind::CONST_RATIONAL) {
      if((*i).getConst<Rational>().isZero()) {
        TNode zero = (*i);
        return RewriteResponse(REWRITE_DONE, zero);
      }
    }
  }
  return RewriteResponse(REWRITE_DONE, t);
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
  Assert(t.getKind()== kind::PLUS);

  if(canFlatten(kind::PLUS, t)){
    return RewriteResponse(REWRITE_DONE, flatten(kind::PLUS, t));
  }else{
    return RewriteResponse(REWRITE_DONE, t);
  }
}

RewriteResponse ArithRewriter::postRewritePlus(TNode t){
  Assert(t.getKind()== kind::PLUS);

  std::vector<Monomial> monomials;
  std::vector<Polynomial> polynomials;

  for(TNode::iterator i = t.begin(), end = t.end(); i != end; ++i){
    TNode curr = *i;
    if(Monomial::isMember(curr)){
      monomials.push_back(Monomial::parseMonomial(curr));
    }else{
      polynomials.push_back(Polynomial::parsePolynomial(curr));
    }
  }

  if(!monomials.empty()){
    Monomial::sort(monomials);
    Monomial::combineAdjacentMonomials(monomials);
    polynomials.push_back(Polynomial::mkPolynomial(monomials));
  }

  Polynomial res = Polynomial::sumPolynomials(polynomials);

  return RewriteResponse(REWRITE_DONE, res.getNode());
}

RewriteResponse ArithRewriter::postRewriteMult(TNode t){
  Assert(t.getKind()== kind::MULT || t.getKind()==kind::NONLINEAR_MULT);

  Polynomial res = Polynomial::mkOne();

  for(TNode::iterator i = t.begin(), end = t.end(); i != end; ++i){
    Node curr = *i;
    Polynomial currPoly = Polynomial::parsePolynomial(curr);

    res = res * currPoly;
  }

  return RewriteResponse(REWRITE_DONE, res.getNode());
}


RewriteResponse ArithRewriter::preRewriteTranscendental(TNode t) {
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteTranscendental(TNode t) { 
  Trace("arith-tf-rewrite") << "Rewrite transcendental function : " << t << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  switch( t.getKind() ){
  case kind::EXPONENTIAL: {
    if(t[0].getKind() == kind::CONST_RATIONAL){
      Node one = nm->mkConst(Rational(1));
      if(t[0].getConst<Rational>().sgn()>=0 && t[0].getType().isInteger() && t[0]!=one){
        return RewriteResponse(
            REWRITE_AGAIN,
            nm->mkNode(kind::POW, nm->mkNode(kind::EXPONENTIAL, one), t[0]));
      }else{          
        return RewriteResponse(REWRITE_DONE, t);
      }
    }else if(t[0].getKind() == kind::PLUS ){
      std::vector<Node> product;
      for( unsigned i=0; i<t[0].getNumChildren(); i++ ){
        product.push_back(nm->mkNode(kind::EXPONENTIAL, t[0][i]));
      }
      return RewriteResponse(REWRITE_AGAIN, nm->mkNode(kind::MULT, product));
    }
  }
    break;
  case kind::SINE:
    if(t[0].getKind() == kind::CONST_RATIONAL){
      const Rational& rat = t[0].getConst<Rational>();
      if(rat.sgn() == 0){
        return RewriteResponse(REWRITE_DONE, nm->mkConst(Rational(0)));
      }
      else if (rat.sgn() == -1)
      {
        Node ret =
            nm->mkNode(kind::UMINUS, nm->mkNode(kind::SINE, nm->mkConst(-rat)));
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
            pi_factor = mkRationalNode(Rational(1));
          }
          else
          {
            pi_factor = itm->second;
          }
          msum.erase(pi);
          if (!msum.empty())
          {
            rem = ArithMSum::mkNode(msum);
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
        Node ntwo = mkRationalNode(Rational(2));
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
            Assert( r.sgn()==-1 );
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
            return RewriteResponse(REWRITE_DONE, mkRationalNode(Rational(0)));
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
                                   mkRationalNode(Rational(r.sgn())));
          }
          else if (r_abs.getDenominator() == six)
          {
            Integer five = Integer(5);
            if (r_abs.getNumerator() == one || r_abs.getNumerator() == five)
            {
              return RewriteResponse(
                  REWRITE_DONE,
                  mkRationalNode(Rational(r.sgn()) / Rational(2)));
            }
          }
        }
      }
    }
    break;
  case kind::COSINE: {
    return RewriteResponse(
        REWRITE_AGAIN_FULL,
        nm->mkNode(kind::SINE,
                   nm->mkNode(kind::MINUS,
                              nm->mkNode(kind::MULT,
                                         nm->mkConst(Rational(1) / Rational(2)),
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
                                      mkRationalNode(Rational(1)),
                                      nm->mkNode(kind::SINE, t[0])));
  }
  break;
  case kind::SECANT:
  {
    return RewriteResponse(REWRITE_AGAIN_FULL,
                           nm->mkNode(kind::DIVISION,
                                      mkRationalNode(Rational(1)),
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

RewriteResponse ArithRewriter::postRewriteAtom(TNode atom){
  if(atom.getKind() == kind::IS_INTEGER) {
    if(atom[0].isConst()) {
      return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(atom[0].getConst<Rational>().isIntegral()));
    }
    if(atom[0].getType().isInteger()) {
      return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
    }
    // not supported, but this isn't the right place to complain
    return RewriteResponse(REWRITE_DONE, atom);
  } else if(atom.getKind() == kind::DIVISIBLE) {
    if(atom[0].isConst()) {
      return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(bool((atom[0].getConst<Rational>() / atom.getOperator().getConst<Divisible>().k).isIntegral())));
    }
    if(atom.getOperator().getConst<Divisible>().k.isOne()) {
      return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
    }
    return RewriteResponse(REWRITE_AGAIN, NodeManager::currentNM()->mkNode(kind::EQUAL, NodeManager::currentNM()->mkNode(kind::INTS_MODULUS_TOTAL, atom[0], NodeManager::currentNM()->mkConst(Rational(atom.getOperator().getConst<Divisible>().k))), NodeManager::currentNM()->mkConst(Rational(0))));
  }

  // left |><| right
  TNode left = atom[0];
  TNode right = atom[1];

  Polynomial pleft = Polynomial::parsePolynomial(left);
  Polynomial pright = Polynomial::parsePolynomial(right);

  Debug("arith::rewriter") << "pleft " << pleft.getNode() << std::endl;
  Debug("arith::rewriter") << "pright " << pright.getNode() << std::endl;

  Comparison cmp = Comparison::mkComparison(atom.getKind(), pleft, pright);
  Assert(cmp.isNormalForm());
  return RewriteResponse(REWRITE_DONE, cmp.getNode());
}

RewriteResponse ArithRewriter::preRewriteAtom(TNode atom){
  Assert(isAtom(atom));

  NodeManager* currNM = NodeManager::currentNM();

  if(atom.getKind() == kind::EQUAL) {
    if(atom[0] == atom[1]) {
      return RewriteResponse(REWRITE_DONE, currNM->mkConst(true));
    }
  }else if(atom.getKind() == kind::GT){
    Node leq = currNM->mkNode(kind::LEQ, atom[0], atom[1]);
    return RewriteResponse(REWRITE_DONE, currNM->mkNode(kind::NOT, leq));
  }else if(atom.getKind() == kind::LT){
    Node geq = currNM->mkNode(kind::GEQ, atom[0], atom[1]);
    return RewriteResponse(REWRITE_DONE, currNM->mkNode(kind::NOT, geq));
  }else if(atom.getKind() == kind::IS_INTEGER){
    if(atom[0].getType().isInteger()){
      return RewriteResponse(REWRITE_DONE, currNM->mkConst(true));
    }
  }else if(atom.getKind() == kind::DIVISIBLE){
    if(atom.getOperator().getConst<Divisible>().k.isOne()){
      return RewriteResponse(REWRITE_DONE, currNM->mkConst(true));
    }
  }

  return RewriteResponse(REWRITE_DONE, atom);
}

RewriteResponse ArithRewriter::postRewrite(TNode t){
  if(isTerm(t)){
    RewriteResponse response = postRewriteTerm(t);
    if(Debug.isOn("arith::rewriter") && response.status == REWRITE_DONE) {
      Polynomial::parsePolynomial(response.node);
    }
    return response;
  }else if(isAtom(t)){
    RewriteResponse response = postRewriteAtom(t);
    if(Debug.isOn("arith::rewriter") && response.status == REWRITE_DONE) {
      Comparison::parseNormalForm(response.node);
    }
    return response;
  }else{
    Unreachable();
  }
}

RewriteResponse ArithRewriter::preRewrite(TNode t){
  if(isTerm(t)){
    return preRewriteTerm(t);
  }else if(isAtom(t)){
    return preRewriteAtom(t);
  }else{
    Unreachable();
  }
}

Node ArithRewriter::makeUnaryMinusNode(TNode n){
  Rational qNegOne(-1);
  return NodeManager::currentNM()->mkNode(kind::MULT, mkRationalNode(qNegOne),n);
}

Node ArithRewriter::makeSubtractionNode(TNode l, TNode r){
  Node negR = makeUnaryMinusNode(r);
  Node diff = NodeManager::currentNM()->mkNode(kind::PLUS, l, negR);

  return diff;
}

RewriteResponse ArithRewriter::rewriteDiv(TNode t, bool pre){
  Assert(t.getKind() == kind::DIVISION_TOTAL || t.getKind()== kind::DIVISION);

  Node left = t[0];
  Node right = t[1];
  if(right.getKind() == kind::CONST_RATIONAL){
    const Rational& den = right.getConst<Rational>();

    if(den.isZero()){
      if(t.getKind() == kind::DIVISION_TOTAL){
        return RewriteResponse(REWRITE_DONE, mkRationalNode(0));
      }else{
        // This is unsupported, but this is not a good place to complain
        return RewriteResponse(REWRITE_DONE, t);
      }
    }
    Assert(den != Rational(0));

    if(left.getKind() == kind::CONST_RATIONAL){
      const Rational& num = left.getConst<Rational>();
      Rational div = num / den;
      Node result =  mkRationalNode(div);
      return RewriteResponse(REWRITE_DONE, result);
    }

    Rational div = den.inverse();

    Node result = mkRationalNode(div);

    Node mult = NodeManager::currentNM()->mkNode(kind::MULT,left,result);
    if(pre){
      return RewriteResponse(REWRITE_DONE, mult);
    }else{
      return RewriteResponse(REWRITE_AGAIN, mult);
    }
  }else{
    return RewriteResponse(REWRITE_DONE, t);
  }
}

RewriteResponse ArithRewriter::rewriteIntsDivModTotal(TNode t, bool pre){
  Kind k = t.getKind();
  // Assert(k == kind::INTS_MODULUS || k == kind::INTS_MODULUS_TOTAL ||
  //        k == kind::INTS_DIVISION || k == kind::INTS_DIVISION_TOTAL);

  //Leaving the function as before (INTS_MODULUS can be handled),
  // but restricting its use here
  Assert(k == kind::INTS_MODULUS_TOTAL || k == kind::INTS_DIVISION_TOTAL);
  TNode n = t[0], d = t[1];
  bool dIsConstant = d.getKind() == kind::CONST_RATIONAL;
  if(dIsConstant && d.getConst<Rational>().isZero()){
    if(k == kind::INTS_MODULUS_TOTAL || k == kind::INTS_DIVISION_TOTAL){
      return RewriteResponse(REWRITE_DONE, mkRationalNode(0));
    }else{
      // Do nothing for k == INTS_MODULUS
      return RewriteResponse(REWRITE_DONE, t);
    }
  }else if(dIsConstant && d.getConst<Rational>().isOne()){
    if(k == kind::INTS_MODULUS || k == kind::INTS_MODULUS_TOTAL){
      return RewriteResponse(REWRITE_DONE, mkRationalNode(0));
    }else{
      Assert(k == kind::INTS_DIVISION || k == kind::INTS_DIVISION_TOTAL);
      return RewriteResponse(REWRITE_AGAIN, n);
    }
  }
  else if (dIsConstant && d.getConst<Rational>().sgn() < 0)
  {
    // pull negation
    //   (div x (- c)) ---> (- (div x c))
    //   (mod x (- c)) ---> (mod x c)
    NodeManager* nm = NodeManager::currentNM();
    Node nn = nm->mkNode(k, t[0], nm->mkConst(-t[1].getConst<Rational>()));
    Node ret = k == kind::INTS_DIVISION ? nm->mkNode(kind::UMINUS, nn) : nn;
    return RewriteResponse(REWRITE_AGAIN, nn);
  }else if(dIsConstant && n.getKind() == kind::CONST_RATIONAL){
    Assert(d.getConst<Rational>().isIntegral());
    Assert(n.getConst<Rational>().isIntegral());
    Assert(!d.getConst<Rational>().isZero());
    Integer di = d.getConst<Rational>().getNumerator();
    Integer ni = n.getConst<Rational>().getNumerator();

    bool isDiv = (k == kind::INTS_DIVISION || k == kind::INTS_DIVISION_TOTAL);

    Integer result = isDiv ? ni.euclidianDivideQuotient(di) : ni.euclidianDivideRemainder(di);

    Node resultNode = mkRationalNode(Rational(result));
    return RewriteResponse(REWRITE_DONE, resultNode);
  }else{
    return RewriteResponse(REWRITE_DONE, t);
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
