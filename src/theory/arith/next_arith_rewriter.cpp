/*********************                                                        */
/*! \file next_arith_rewriter.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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
#include "theory/arith/next_arith_rewriter.h"
#include "theory/arith/arith_utilities.h"

#include <vector>
#include <set>
#include <stack>


using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

bool isVariable(TNode t){
  return t.getMetaKind() == kind::metakind::VARIABLE;
}

RewriteResponse NextArithRewriter::rewriteConstant(TNode t){
  Assert(t.getMetaKind() == kind::metakind::CONSTANT);
  Node val = coerceToRationalNode(t);

  return RewriteComplete(val);
}

RewriteResponse NextArithRewriter::rewriteVariable(TNode t){
  Assert(isVariable(t));

  return RewriteComplete(t);
}

RewriteResponse NextArithRewriter::rewriteMinus(TNode t, bool pre){
  Assert(t.getKind()== kind::MINUS);

  if(t[0] == t[1]) return RewriteComplete(d_constants->d_ZERO_NODE);

  Node noMinus = makeSubtractionNode(t[0],t[1]);
  if(pre){
    return RewriteComplete(noMinus);
  }else{
    return FullRewriteNeeded(noMinus);
  }
}

RewriteResponse NextArithRewriter::rewriteUMinus(TNode t, bool pre){
  Assert(t.getKind()== kind::UMINUS);

  Node noUminus = makeUnaryMinusNode(t[0]);
  if(pre)
    return RewriteComplete(noUminus);
  else
    return RewriteAgain(noUminus);
}

RewriteResponse NextArithRewriter::preRewriteTerm(TNode t){
  if(t.getMetaKind() == kind::metakind::CONSTANT){
    return rewriteConstant(t);
  }else if(isVariable(t)){
    return rewriteVariable(t);
  }else if(t.getKind() == kind::MINUS){
    return rewriteMinus(t, true);
  }else if(t.getKind() == kind::UMINUS){
    return rewriteUMinus(t, true);
  }else if(t.getKind() == kind::DIVISION){
    if(t[0].getKind()== kind::CONST_RATIONAL){
      return rewriteDivByConstant(t, true);
    }else{
      return RewriteComplete(t);
    }
  }else if(t.getKind() == kind::PLUS){
    return preRewritePlus(t);
  }else if(t.getKind() == kind::MULT){
    return preRewriteMult(t);
  }else{
    Unreachable();
  }
}
RewriteResponse NextArithRewriter::postRewriteTerm(TNode t){
  if(t.getMetaKind() == kind::metakind::CONSTANT){
    return rewriteConstant(t);
  }else if(isVariable(t)){
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
  }else{
    Unreachable();
  }
}

RewriteResponse NextArithRewriter::preRewriteMult(TNode t){
  Assert(t.getKind()== kind::MULT);

  // Rewrite multiplications with a 0 argument and to 0
  Integer intZero;

  for(TNode::iterator i = t.begin(); i != t.end(); ++i) {
    if((*i).getKind() == kind::CONST_RATIONAL) {
      if((*i).getConst<Rational>() == d_constants->d_ZERO) {
        return RewriteComplete(d_constants->d_ZERO_NODE);
      }
    } else if((*i).getKind() == kind::CONST_INTEGER) {
      if((*i).getConst<Integer>() == intZero) {
        if(t.getType().isInteger()) {
          return RewriteComplete(NodeManager::currentNM()->mkConst(intZero));
        } else {
          return RewriteComplete(d_constants->d_ZERO_NODE);
        }
      }
    }
  }
  return RewriteComplete(t);
}
RewriteResponse NextArithRewriter::preRewritePlus(TNode t){
  Assert(t.getKind()== kind::PLUS);

  return RewriteComplete(t);
}

RewriteResponse NextArithRewriter::postRewritePlus(TNode t){
  Assert(t.getKind()== kind::PLUS);

  Polynomial res = Polynomial::mkZero();

  for(TNode::iterator i = t.begin(), end = t.end(); i != end; ++i){
    Node curr = *i;
    Polynomial currPoly = Polynomial::parsePolynomial(curr);

    res = res + currPoly;
  }

  return RewriteComplete(res.getNode());
}

RewriteResponse NextArithRewriter::postRewriteMult(TNode t){
  Assert(t.getKind()== kind::MULT);

  Polynomial res = Polynomial::mkOne();

  for(TNode::iterator i = t.begin(), end = t.end(); i != end; ++i){
    Node curr = *i;
    Polynomial currPoly = Polynomial::parsePolynomial(curr);

    res = res * currPoly;
  }

  return RewriteComplete(res.getNode());
}

RewriteResponse NextArithRewriter::postRewriteAtomConstantRHS(TNode t){
  TNode left  = t[0];
  TNode right = t[1];


  Comparison cmp = Comparison::mkComparison(t.getKind(), Polynomial::parsePolynomial(left), Constant(right));

  if(cmp.isBoolean()){
    return RewriteComplete(cmp.getNode());
  }

  if(cmp.getLeft().containsConstant()){
    Monomial constantHead = cmp.getLeft().getHead();
    Assert(constantHead.isConstant());

    Constant constant = constantHead.getConstant();

    Constant negativeConstantHead = -constant;

    cmp = cmp.addConstant(negativeConstantHead);
  }
  Assert(!cmp.getLeft().containsConstant());

  if(!cmp.getLeft().getHead().coefficientIsOne()){
    Monomial constantHead = cmp.getLeft().getHead();
    Assert(!constantHead.isConstant());
    Constant constant = constantHead.getConstant();

    Constant inverse = Constant::mkConstant(constant.getValue().inverse());

    cmp = cmp.multiplyConstant(inverse);
  }
  Assert(cmp.getLeft().getHead().coefficientIsOne());

  Assert(cmp.isBoolean() || cmp.isNormalForm());
  return RewriteComplete(cmp.getNode());
}

RewriteResponse NextArithRewriter::postRewriteAtom(TNode atom){
  // left |><| right
  TNode left = atom[0];
  TNode right = atom[1];

  if(right.getMetaKind() == kind::metakind::CONSTANT){
    return postRewriteAtomConstantRHS(atom);
  }else{
    //Transform this to: (left - right) |><| 0
    Node diff = makeSubtractionNode(left, right);
    Node reduction = NodeManager::currentNM()->mkNode(atom.getKind(), diff, d_constants->d_ZERO_NODE);
    return FullRewriteNeeded(reduction);
  }
}

RewriteResponse NextArithRewriter::preRewriteAtom(TNode atom){
  Assert(isAtom(atom));
  NodeManager* currNM = NodeManager::currentNM();

  if(atom.getKind() == kind::EQUAL) {
    if(atom[0] == atom[1]) {
      return RewriteComplete(currNM->mkConst(true));
    }
  }

  Node reduction = atom;

  if(atom[1].getMetaKind() != kind::metakind::CONSTANT){
    // left |><| right
    TNode left = atom[0];
    TNode right = atom[1];

    //Transform this to: (left - right) |><| 0
    Node diff = makeSubtractionNode(left, right);
    reduction = currNM->mkNode(atom.getKind(), diff, d_constants->d_ZERO_NODE);
  }

  if(reduction.getKind() == kind::GT){
    Node leq = currNM->mkNode(kind::LEQ, reduction[0], reduction[1]);
    reduction = currNM->mkNode(kind::NOT, leq);
  }else if(reduction.getKind() == kind::LT){
    Node geq = currNM->mkNode(kind::GEQ, reduction[0], reduction[1]);
    reduction = currNM->mkNode(kind::NOT, geq);
  }

  return RewriteComplete(reduction);
}

RewriteResponse NextArithRewriter::postRewrite(TNode t){
  if(isTerm(t)){
    RewriteResponse response = postRewriteTerm(t);
    if(Debug.isOn("arith::rewriter") && response.isDone()) {
      Polynomial::parsePolynomial(response.getNode());
    }
    return response;
  }else if(isAtom(t)){
    RewriteResponse response = postRewriteAtom(t);
    if(Debug.isOn("arith::rewriter") && response.isDone()) {
      Comparison::parseNormalForm(response.getNode());
    }
    return response;
  }else{
    Unreachable();
    return RewriteComplete(Node::null());
  }
}

RewriteResponse NextArithRewriter::preRewrite(TNode t){
  if(isTerm(t)){
    return preRewriteTerm(t);
  }else if(isAtom(t)){
    return preRewriteAtom(t);
  }else{
    Unreachable();
    return RewriteComplete(Node::null());
  }
}

Node NextArithRewriter::makeUnaryMinusNode(TNode n){
  return NodeManager::currentNM()->mkNode(kind::MULT,d_constants->d_NEGATIVE_ONE_NODE,n);
}

Node NextArithRewriter::makeSubtractionNode(TNode l, TNode r){
  Node negR = makeUnaryMinusNode(r);
  Node diff = NodeManager::currentNM()->mkNode(kind::PLUS, l, negR);

  return diff;
}

RewriteResponse NextArithRewriter::rewriteDivByConstant(TNode t, bool pre){
  Assert(t.getKind()== kind::DIVISION);

  Node left = t[0];
  Node right = t[1];
  Assert(right.getKind()== kind::CONST_RATIONAL);


  const Rational& den = right.getConst<Rational>();

  Assert(den != d_constants->d_ZERO);

  Rational div = den.inverse();

  Node result = mkRationalNode(div);

  Node mult = NodeManager::currentNM()->mkNode(kind::MULT,left,result);
  if(pre){
    return RewriteComplete(mult);
  }else{
    return RewriteAgain(mult);
  }
}
