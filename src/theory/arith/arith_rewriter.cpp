/*********************                                                        */
/*! \file arith_rewriter.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/theory.h"
#include "theory/arith/normal_form.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/arith_utilities.h"

#include <vector>
#include <set>
#include <stack>

namespace CVC4 {
namespace theory {
namespace arith {

bool ArithRewriter::isAtom(TNode n) {
  return arith::isRelationOperator(n.getKind());
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
  }else if(t.getKind() == kind::MINUS){
    return rewriteMinus(t, true);
  }else if(t.getKind() == kind::UMINUS){
    return rewriteUMinus(t, true);
  }else if(t.getKind() == kind::DIVISION){
    return RewriteResponse(REWRITE_DONE, t); // wait until t[1] is rewritten
  }else if(t.getKind() == kind::PLUS){
    return preRewritePlus(t);
  }else if(t.getKind() == kind::MULT){
    return preRewriteMult(t);
  }else if(t.getKind() == kind::INTS_DIVISION){
    Rational intOne(1);
    if(t[1].getKind()== kind::CONST_RATIONAL && t[1].getConst<Rational>() == intOne){
      return RewriteResponse(REWRITE_AGAIN, t[0]);
    }else{
      return RewriteResponse(REWRITE_DONE, t);
    }
  }else if(t.getKind() == kind::INTS_MODULUS){
    Rational intOne(1);
    if(t[1].getKind()== kind::CONST_RATIONAL && t[1].getConst<Rational>() == intOne){
      Rational intZero(0);
      return RewriteResponse(REWRITE_AGAIN, mkRationalNode(intZero));
    }else{
      return RewriteResponse(REWRITE_DONE, t);
    }
  }else{
    Unreachable();
  }
}
RewriteResponse ArithRewriter::postRewriteTerm(TNode t){
  if(t.isConst()){
    return rewriteConstant(t);
  }else if(t.isVar()){
    return rewriteVariable(t);
  }else if(t.getKind() == kind::MINUS){
    return rewriteMinus(t, false);
  }else if(t.getKind() == kind::UMINUS){
    return rewriteUMinus(t, false);
  }else if(t.getKind() == kind::DIVISION){
    return rewriteDivByConstant(t, false);
  }else if(t.getKind() == kind::PLUS){
    return postRewritePlus(t);
  }else if(t.getKind() == kind::MULT){
    return postRewriteMult(t);
  }else if(t.getKind() == kind::INTS_DIVISION){
    return RewriteResponse(REWRITE_DONE, t);
  }else if(t.getKind() == kind::INTS_MODULUS){
    return RewriteResponse(REWRITE_DONE, t);
  }else{
    Unreachable();
  }
}

RewriteResponse ArithRewriter::preRewriteMult(TNode t){
  Assert(t.getKind()== kind::MULT);

  // Rewrite multiplications with a 0 argument and to 0
  Rational qZero(0);

  for(TNode::iterator i = t.begin(); i != t.end(); ++i) {
    if((*i).getKind() == kind::CONST_RATIONAL) {
      if((*i).getConst<Rational>() == qZero) {
        return RewriteResponse(REWRITE_DONE, mkRationalNode(qZero));
      }
    }
  }
  return RewriteResponse(REWRITE_DONE, t);
}
RewriteResponse ArithRewriter::preRewritePlus(TNode t){
  Assert(t.getKind()== kind::PLUS);

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewritePlus(TNode t){
  Assert(t.getKind()== kind::PLUS);

  Polynomial res = Polynomial::mkZero();

  for(TNode::iterator i = t.begin(), end = t.end(); i != end; ++i){
    Node curr = *i;
    Polynomial currPoly = Polynomial::parsePolynomial(curr);

    res = res + currPoly;
  }

  return RewriteResponse(REWRITE_DONE, res.getNode());
}

RewriteResponse ArithRewriter::postRewriteMult(TNode t){
  Assert(t.getKind()== kind::MULT);

  Polynomial res = Polynomial::mkOne();

  for(TNode::iterator i = t.begin(), end = t.end(); i != end; ++i){
    Node curr = *i;
    Polynomial currPoly = Polynomial::parsePolynomial(curr);

    res = res * currPoly;
  }

  return RewriteResponse(REWRITE_DONE, res.getNode());
}

// RewriteResponse ArithRewriter::postRewriteAtomConstantRHS(TNode t){
//   TNode left  = t[0];
//   TNode right = t[1];

//   Polynomial pLeft = Polynomial::parsePolynomial(left);
  

//   Comparison cmp = Comparison::mkComparison(t.getKind(), Polynomial::parsePolynomial(left), Constant(right));

//   Assert(cmp.isNormalForm());
//   return RewriteResponse(REWRITE_DONE, cmp.getNode());
// }

RewriteResponse ArithRewriter::postRewriteAtom(TNode atom){
  // left |><| right
  TNode left = atom[0];
  TNode right = atom[1];

  Polynomial pleft = Polynomial::parsePolynomial(left);
  Polynomial pright = Polynomial::parsePolynomial(right);

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
    return RewriteResponse(REWRITE_DONE, Node::null());
  }
}

RewriteResponse ArithRewriter::preRewrite(TNode t){
  if(isTerm(t)){
    return preRewriteTerm(t);
  }else if(isAtom(t)){
    return preRewriteAtom(t);
  }else{
    Unreachable();
    return RewriteResponse(REWRITE_DONE, Node::null());
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

RewriteResponse ArithRewriter::rewriteDivByConstant(TNode t, bool pre){
  Assert(t.getKind()== kind::DIVISION);

  Node left = t[0];
  Node right = t[1];
  Assert(right.getKind()== kind::CONST_RATIONAL);


  const Rational& den = right.getConst<Rational>();

  Assert(den != Rational(0));

  Rational div = den.inverse();

  Node result = mkRationalNode(div);

  Node mult = NodeManager::currentNM()->mkNode(kind::MULT,left,result);
  if(pre){
    return RewriteResponse(REWRITE_DONE, mult);
  }else{
    return RewriteResponse(REWRITE_AGAIN, mult);
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
