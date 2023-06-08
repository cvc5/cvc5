/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

#include <optional>
#include <set>
#include <sstream>
#include <stack>
#include <vector>

#include "expr/algorithm/flatten.h"
#include "smt/logic_exception.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/operator_elim.h"
#include "theory/arith/rewriter/addition.h"
#include "theory/arith/rewriter/node_utils.h"
#include "theory/arith/rewriter/ordering.h"
#include "theory/arith/rewriter/rewrite_atom.h"
#include "theory/theory.h"
#include "util/bitvector.h"
#include "util/divisible.h"
#include "util/iand.h"
#include "util/real_algebraic_number.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {

ArithRewriter::ArithRewriter(OperatorElim& oe) : d_opElim(oe) {}

RewriteResponse ArithRewriter::preRewrite(TNode t)
{
  Trace("arith-rewriter") << "preRewrite(" << t << ")" << std::endl;
  if (rewriter::isAtom(t))
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
  if (rewriter::isAtom(t))
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
  Assert(rewriter::isAtom(atom));

  Kind kind = atom.getKind();
  if (atom.getNumChildren() == 2)
  {
    if (auto response =
            rewriter::tryEvaluateRelationReflexive(kind, atom[0], atom[1]);
        response)
    {
      return RewriteResponse(REWRITE_DONE, rewriter::mkConst(*response));
    }
  }

  switch (kind)
  {
    case Kind::GT:
      return RewriteResponse(
          REWRITE_DONE,
          rewriter::buildRelation(kind::LEQ, atom[0], atom[1], true));
    case Kind::LT:
      return RewriteResponse(
          REWRITE_DONE,
          rewriter::buildRelation(kind::GEQ, atom[0], atom[1], true));
    case Kind::IS_INTEGER:
      if (atom[0].getType().isInteger())
      {
        return RewriteResponse(REWRITE_DONE, rewriter::mkConst(true));
      }
      break;
    case Kind::DIVISIBLE:
      if (atom.getOperator().getConst<Divisible>().k.isOne())
      {
        return RewriteResponse(REWRITE_DONE, rewriter::mkConst(true));
      }
      break;
    default:;
  }

  return RewriteResponse(REWRITE_DONE, atom);
}

RewriteResponse ArithRewriter::postRewriteAtom(TNode atom)
{
  Assert(rewriter::isAtom(atom));
  Trace("arith-rewriter") << "postRewriteAtom: " << atom << std::endl;

  if (atom.getKind() == kind::IS_INTEGER)
  {
    return rewriteExtIntegerOp(atom);
  }
  else if (atom.getKind() == kind::DIVISIBLE)
  {
    const Integer& k = atom.getOperator().getConst<Divisible>().k;
    if (atom[0].isConst())
    {
      const Rational& num = atom[0].getConst<Rational>();
      return RewriteResponse(REWRITE_DONE,
                             rewriter::mkConst((num / k).isIntegral()));
    }
    if (k.isOne())
    {
      return RewriteResponse(REWRITE_DONE, rewriter::mkConst(true));
    }
    NodeManager* nm = NodeManager::currentNM();
    return RewriteResponse(
        REWRITE_AGAIN,
        nm->mkNode(
            kind::EQUAL,
            nm->mkNode(kind::INTS_MODULUS_TOTAL, atom[0], rewriter::mkConst(k)),
            rewriter::mkConst(Integer(0))));
  }
  // left |><| right
  Kind kind = atom.getKind();
  Node left = rewriter::removeToReal(atom[0]);
  Node right = rewriter::removeToReal(atom[1]);

  if (auto response = rewriter::tryEvaluateRelationReflexive(kind, left, right);
      response)
  {
    return RewriteResponse(REWRITE_DONE, rewriter::mkConst(*response));
  }

  Assert(isRelationOperator(kind));

  if (auto response = rewriter::tryEvaluateRelation(kind, left, right);
      response)
  {
    return RewriteResponse(REWRITE_DONE, rewriter::mkConst(*response));
  }

  bool negate = false;

  switch (atom.getKind())
  {
    case Kind::LEQ:
      kind = Kind::GEQ;
      negate = true;
      break;
    case Kind::LT:
      kind = Kind::GT;
      negate = true;
      break;
    default: break;
  }

  rewriter::Sum sum;
  rewriter::addToSum(sum, left, negate);
  rewriter::addToSum(sum, right, !negate);

  // Now we have (sum <kind> 0)
  if (rewriter::isIntegral(sum))
  {
    if (kind == Kind::EQUAL)
    {
      return RewriteResponse(REWRITE_DONE,
                             rewriter::buildIntegerEquality(std::move(sum)));
    }
    return RewriteResponse(
        REWRITE_DONE, rewriter::buildIntegerInequality(std::move(sum), kind));
  }
  else
  {
    if (kind == Kind::EQUAL)
    {
      return RewriteResponse(REWRITE_DONE,
                             rewriter::buildRealEquality(std::move(sum)));
    }
    return RewriteResponse(REWRITE_DONE,
                           rewriter::buildRealInequality(std::move(sum), kind));
  }
}

RewriteResponse ArithRewriter::preRewriteTerm(TNode t){
  if(t.isConst()){
    return RewriteResponse(REWRITE_DONE, t);
  }else if(t.isVar()){
    return rewriteVariable(t);
  }else{
    switch(Kind k = t.getKind()){
      case kind::REAL_ALGEBRAIC_NUMBER: return rewriteRAN(t);
      case kind::SUB: return rewriteSub(t);
      case kind::NEG: return rewriteNeg(t, true);
      case kind::DIVISION:
      case kind::DIVISION_TOTAL: return rewriteDiv(t, true);
      case kind::ADD: return preRewritePlus(t);
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
      case kind::TO_INTEGER:
      case kind::TO_REAL:
      case kind::POW:
      case kind::PI: return RewriteResponse(REWRITE_DONE, t);
      default: Unhandled() << k;
    }
  }
}

RewriteResponse ArithRewriter::postRewriteTerm(TNode t){
  if(t.isConst()){
    return RewriteResponse(REWRITE_DONE, t);
  }else if(t.isVar()){
    return rewriteVariable(t);
  }
  else
  {
    Trace("arith-rewriter") << "postRewriteTerm: " << t << std::endl;
    switch(t.getKind()){
      case kind::REAL_ALGEBRAIC_NUMBER: return rewriteRAN(t);
      case kind::SUB: return rewriteSub(t);
      case kind::NEG: return rewriteNeg(t, false);
      case kind::DIVISION:
      case kind::DIVISION_TOTAL: return rewriteDiv(t, false);
      case kind::ADD: return postRewritePlus(t);
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
      case kind::TO_REAL: return rewriteToReal(t);
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
            cvc5::internal::Rational r(expr::NodeValue::MAX_CHILDREN);
            if (exp <= r)
            {
              unsigned num = exp.getNumerator().toUnsignedInt();
              Node ret;
              if( num==1 ){
                ret = base;
              }else{
                NodeBuilder nb(kind::MULT);
                for(unsigned i=0; i < num; ++i){
                  nb << base;
                }
                Assert(nb.getNumChildren() > 0);
                ret = nb;
              }
              // ensure type is preserved
              if (t.getType().isReal())
              {
                ret = rewriter::ensureReal(ret);
              }
              return RewriteResponse(REWRITE_AGAIN, ret);
            }
          }
        }
        else if (t[0].isConst()
                 && t[0].getConst<Rational>().getNumerator().toUnsignedInt()
                        == 2
                 && t[1].getType().isInteger())
        {
          Node ret = NodeManager::currentNM()->mkNode(kind::POW2, t[1]);
          // ensure type is preserved
          if (t.getType().isReal())
          {
            ret = rewriter::ensureReal(ret);
          }
          return RewriteResponse(REWRITE_AGAIN, ret);
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
      case kind::PI: return RewriteResponse(REWRITE_DONE, t);
      default: Unreachable();
    }
  }
}

RewriteResponse ArithRewriter::rewriteRAN(TNode t)
{
  Assert(rewriter::isRAN(t));
  Assert(t.getType().isReal());
  const RealAlgebraicNumber& r = rewriter::getRAN(t);
  if (r.isRational())
  {
    return RewriteResponse(REWRITE_DONE, rewriter::mkConst(r.toRational()));
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteVariable(TNode t)
{
  Assert(t.isVar());

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteNeg(TNode t, bool pre)
{
  Assert(t.getKind() == kind::NEG);

  NodeManager* nm = NodeManager::currentNM();
  if (t[0].isConst())
  {
    Rational neg = -(t[0].getConst<Rational>());
    return RewriteResponse(REWRITE_DONE,
                           nm->mkConstRealOrInt(t.getType(), neg));
  }
  if (rewriter::isRAN(t[0]))
  {
    return RewriteResponse(REWRITE_DONE,
                           rewriter::mkConst(-rewriter::getRAN(t[0])));
  }

  Node noUminus = nm->mkNode(kind::MULT, rewriter::mkConst(Rational(-1)), t[0]);
  if (pre)
  {
    return RewriteResponse(REWRITE_DONE, noUminus);
  }
  else
  {
    return RewriteResponse(REWRITE_AGAIN, noUminus);
  }
}

RewriteResponse ArithRewriter::rewriteSub(TNode t)
{
  Assert(t.getKind() == kind::SUB);
  Assert(t.getNumChildren() == 2);

  NodeManager* nm = NodeManager::currentNM();
  if (t[0] == t[1])
  {
    return RewriteResponse(REWRITE_DONE,
                           nm->mkConstRealOrInt(t.getType(), Rational(0)));
  }
  return RewriteResponse(
      REWRITE_AGAIN_FULL,
      nm->mkNode(Kind::ADD,
                 t[0],
                 nm->mkNode(kind::MULT,
                            nm->mkConstRealOrInt(t[1].getType(), Rational(-1)),
                            t[1])));
}

RewriteResponse ArithRewriter::preRewritePlus(TNode t)
{
  Assert(t.getKind() == kind::ADD);
  return RewriteResponse(REWRITE_DONE, expr::algorithm::flatten(t));
}

RewriteResponse ArithRewriter::postRewritePlus(TNode t)
{
  Assert(t.getKind() == kind::ADD);
  Assert(t.getNumChildren() > 1);

  std::vector<TNode> children;
  expr::algorithm::flatten(t, children, Kind::ADD, Kind::TO_REAL);

  rewriter::Sum sum;
  for (const auto& child : children)
  {
    rewriter::addToSum(sum, child);
  }
  Node retSum = rewriter::collectSum(sum);
  retSum = rewriter::maybeEnsureReal(t.getType(), retSum);
  return RewriteResponse(REWRITE_DONE, retSum);
}

RewriteResponse ArithRewriter::preRewriteMult(TNode node)
{
  Assert(node.getKind() == kind::MULT
         || node.getKind() == kind::NONLINEAR_MULT);

  if (auto res = rewriter::getZeroChild(node); res)
  {
    return RewriteResponse(REWRITE_DONE,
                           rewriter::maybeEnsureReal(node.getType(), *res));
  }
  return RewriteResponse(REWRITE_DONE, node);
}

RewriteResponse ArithRewriter::postRewriteMult(TNode t){
  Assert(t.getKind() == kind::MULT || t.getKind() == kind::NONLINEAR_MULT);
  Assert(t.getNumChildren() >= 2);

  std::vector<TNode> children;
  expr::algorithm::flatten(t, children, Kind::MULT, Kind::NONLINEAR_MULT, Kind::TO_REAL);

  if (auto res = rewriter::getZeroChild(children); res)
  {
    return RewriteResponse(REWRITE_DONE,
                           rewriter::maybeEnsureReal(t.getType(), *res));
  }

  Node ret;
  // Distribute over addition
  if (std::any_of(children.begin(), children.end(), [](TNode child) {
        return child.getKind() == Kind::ADD;
      }))
  {
    ret = rewriter::distributeMultiplication(children);
  }
  else
  {
    RealAlgebraicNumber ran = RealAlgebraicNumber(Integer(1));
    std::vector<Node> leafs;

    for (const auto& child : children)
    {
      if (child.isConst())
      {
        if (child.getConst<Rational>().isZero())
        {
          return RewriteResponse(REWRITE_DONE,
                                 rewriter::maybeEnsureReal(t.getType(), child));
        }
        ran *= child.getConst<Rational>();
      }
      else if (rewriter::isRAN(child))
      {
        ran *= rewriter::getRAN(child);
      }
      else
      {
        leafs.emplace_back(child);
      }
    }
    ret = rewriter::mkMultTerm(ran, std::move(leafs));
  }
  ret = rewriter::maybeEnsureReal(t.getType(), ret);
  return RewriteResponse(REWRITE_DONE, ret);
}

RewriteResponse ArithRewriter::rewriteDiv(TNode t, bool pre)
{
  Assert(t.getKind() == kind::DIVISION_TOTAL || t.getKind() == kind::DIVISION);
  Assert(t.getNumChildren() == 2);

  Node left = rewriter::removeToReal(t[0]);
  Node right = rewriter::removeToReal(t[1]);
  NodeManager* nm = NodeManager::currentNM();
  if (right.isConst())
  {
    const Rational& den = right.getConst<Rational>();

    if (den.isZero())
    {
      if (t.getKind() == kind::DIVISION_TOTAL)
      {
        Node ret = nm->mkConstReal(0);
        return RewriteResponse(REWRITE_DONE, ret);
      }
      else
      {
        Node ret = nm->mkNode(t.getKind(), left, right);
        return RewriteResponse(REWRITE_DONE, ret);
      }
    }
    Assert(den != Rational(0));

    if (left.isConst())
    {
      const Rational& num = left.getConst<Rational>();
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(num / den));
    }
    if (rewriter::isRAN(left))
    {
      return RewriteResponse(REWRITE_DONE,
                             rewriter::ensureReal(nm->mkRealAlgebraicNumber(
                                 rewriter::getRAN(left) / den)));
    }

    Node result = nm->mkConstReal(den.inverse());
    Node mult = rewriter::ensureReal(
        NodeManager::currentNM()->mkNode(kind::MULT, left, result));
    if (pre)
    {
      return RewriteResponse(REWRITE_DONE, mult);
    }
    // requires again full since ensureReal may have added a to_real
    return RewriteResponse(REWRITE_AGAIN_FULL, mult);
  }
  if (rewriter::isRAN(right))
  {
    const RealAlgebraicNumber& den = rewriter::getRAN(right);
    // mkConst is applied to RAN in this block, which are always Real
    if (left.isConst())
    {
      return RewriteResponse(
          REWRITE_DONE,
          rewriter::ensureReal(rewriter::mkConst(
              RealAlgebraicNumber(left.getConst<Rational>()) / den)));
    }
    if (rewriter::isRAN(left))
    {
      return RewriteResponse(REWRITE_DONE,
                             rewriter::ensureReal(rewriter::mkConst(
                                 rewriter::getRAN(left) / den)));
    }

    Node result = rewriter::mkConst(den.inverse());
    Node mult = rewriter::ensureReal(
        NodeManager::currentNM()->mkNode(kind::MULT, left, result));
    if (pre)
    {
      return RewriteResponse(REWRITE_DONE, mult);
    }
    // requires again full since ensureReal may have added a to_real
    return RewriteResponse(REWRITE_AGAIN_FULL, mult);
  }
  // may have changed due to removing to_real
  if (left!=t[0] || right!=t[1])
  {
    Node ret = nm->mkNode(t.getKind(), left, right);
    return RewriteResponse(REWRITE_AGAIN_FULL, ret);
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteToReal(TNode t)
{
  Assert(t.getKind() == kind::TO_REAL);
  if (!t[0].getType().isInteger())
  {
    // if it is already real type, then just return the argument
    return RewriteResponse(REWRITE_DONE, t[0]);
  }
  NodeManager* nm = NodeManager::currentNM();
  if (t[0].isConst())
  {
    // If the argument is constant, return a real constant.
    const Rational& rat = t[0].getConst<Rational>();
    return RewriteResponse(REWRITE_DONE, nm->mkConstReal(rat));
  }
  if (t[0].getKind()==kind::TO_REAL)
  {
    // (to_real (to_real t)) ---> (to_real t)
    return RewriteResponse(REWRITE_DONE, t[0]);
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
  if (rewriter::isRAN(t[0]))
  {
    const RealAlgebraicNumber& ran = rewriter::getRAN(t[0]);
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
  if (dIsConstant && d.getConst<Rational>().isZero())
  {
    // (div x 0) ---> 0 or (mod x 0) ---> 0
    return returnRewrite(t, nm->mkConstInt(0), Rewrite::DIV_MOD_BY_ZERO);
  }
  else if (dIsConstant && d.getConst<Rational>().isOne())
  {
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
                   ? nm->mkNode(kind::NEG, nn)
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

    Integer result = isDiv ? ni.euclidianDivideQuotient(di)
                           : ni.euclidianDivideRemainder(di);

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
    else if (k0 == kind::NONLINEAR_MULT || k0 == kind::MULT || k0 == kind::ADD)
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
        // op is one of { NONLINEAR_MULT, MULT, ADD }.
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
    Node ret = isPred ? nm->mkConst(false) : nm->mkConstInt(Rational(3));
    return returnRewrite(t, ret, Rewrite::INT_EXT_PI);
  }
  else if (t[0].getKind() == kind::TO_REAL)
  {
    Node ret = nm->mkNode(t.getKind(), t[0][0]);
    return returnRewrite(t, ret, Rewrite::INT_EXT_TO_REAL);
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteIAnd(TNode t)
{
  Assert(t.getKind() == kind::IAND);
  uint32_t bsize = t.getOperator().getConst<IntAnd>().d_size;
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
    // ((_ iand k) x x) ---> (mod x 2^k)
    Node twok = nm->mkConstInt(Rational(Integer(2).pow(bsize)));
    Node ret = nm->mkNode(kind::INTS_MODULUS, t[0], twok);
    return RewriteResponse(REWRITE_AGAIN, ret);
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
      // ((_ iand k) 111...1 y) ---> (mod y 2^k)
      Node twok = nm->mkConstInt(Rational(Integer(2).pow(bsize)));
      Node ret = nm->mkNode(kind::INTS_MODULUS, t[1 - i], twok);
      return RewriteResponse(REWRITE_AGAIN, ret);
    }
  }
  return RewriteResponse(REWRITE_DONE, t);
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
      return RewriteResponse(REWRITE_DONE, rewriter::mkConst(Integer(0)));
    }
    // (pow2 t) ---> (pow 2 t) and continue rewriting to eliminate pow
    Node two = rewriter::mkConst(Integer(2));
    Node ret = nm->mkNode(kind::POW, two, t[0]);
    return RewriteResponse(REWRITE_AGAIN, ret);
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::preRewriteTranscendental(TNode t)
{
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteTranscendental(TNode t)
{
  Trace("arith-tf-rewrite")
      << "Rewrite transcendental function : " << t << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  if (t[0].getKind() == TO_REAL)
  {
    // always strip TO_REAL from argument.
    Node ret = nm->mkNode(t.getKind(), t[0][0]);
    return RewriteResponse(REWRITE_AGAIN, ret);
  }
  switch (t.getKind())
  {
    case kind::EXPONENTIAL:
    {
      if (t[0].isConst())
      {
        Node one = rewriter::mkConst(Integer(1));
        if (t[0].getConst<Rational>().sgn() >= 0 && t[0].getType().isInteger()
            && t[0] != one)
        {
          return RewriteResponse(
              REWRITE_AGAIN,
              nm->mkNode(kind::POW, nm->mkNode(kind::EXPONENTIAL, one), t[0]));
        }
        else
        {
          return RewriteResponse(REWRITE_DONE, t);
        }
      }
      else if (t[0].getKind() == kind::ADD)
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
        if (rat.sgn() == 0)
        {
          return RewriteResponse(REWRITE_DONE, nm->mkConstReal(Rational(0)));
        }
        else if (rat.sgn() == -1)
        {
          Node ret = nm->mkNode(kind::NEG,
                                nm->mkNode(kind::SINE, nm->mkConstReal(-rat)));
          return RewriteResponse(REWRITE_AGAIN_FULL, ret);
        }
      }
      else if ((t[0].getKind() == MULT || t[0].getKind() == NONLINEAR_MULT)
               && t[0][0].isConst() && t[0][0].getConst<Rational>().sgn() == -1)
      {
        // sin(-n*x) ---> -sin(n*x)
        std::vector<Node> mchildren(t[0].begin(), t[0].end());
        mchildren[0] = nm->mkConstReal(-t[0][0].getConst<Rational>());
        Node ret = nm->mkNode(
            kind::NEG,
            nm->mkNode(kind::SINE, nm->mkNode(t[0].getKind(), mchildren)));
        return RewriteResponse(REWRITE_AGAIN_FULL, ret);
      }
      else
      {
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
              pi_factor = rewriter::mkConst(Integer(1));
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
        if (!pi_factor.isNull())
        {
          Trace("arith-tf-rewrite-debug")
              << "Process pi factor = " << pi_factor << std::endl;
          Rational r = pi_factor.getConst<Rational>();
          Rational r_abs = r.abs();
          Rational rone = Rational(1);
          Rational rtwo = Rational(2);
          if (r_abs > rone)
          {
            // add/substract 2*pi beyond scope
            Rational ra_div_two = (r_abs + rone) / rtwo;
            Node new_pi_factor;
            if (r.sgn() == 1)
            {
              new_pi_factor = nm->mkConstReal(r - rtwo * ra_div_two.floor());
            }
            else
            {
              Assert(r.sgn() == -1);
              new_pi_factor = nm->mkConstReal(r + rtwo * ra_div_two.floor());
            }
            Node new_arg = nm->mkNode(kind::MULT, new_pi_factor, pi);
            if (!rem.isNull())
            {
              new_arg = nm->mkNode(kind::ADD, new_arg, rem);
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
              return RewriteResponse(REWRITE_DONE,
                                     nm->mkConstReal(Rational(0)));
            }
            else
            {
              return RewriteResponse(
                  REWRITE_AGAIN_FULL,
                  nm->mkNode(kind::NEG, nm->mkNode(kind::SINE, rem)));
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
    case kind::COSINE:
    {
      return RewriteResponse(
          REWRITE_AGAIN_FULL,
          nm->mkNode(
              kind::SINE,
              nm->mkNode(kind::SUB,
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
    default: break;
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
  Trace("arith-rewriter") << "ArithRewriter : " << t << " == " << ret << " by "
                          << r << std::endl;
  return RewriteResponse(REWRITE_AGAIN_FULL, ret);
}

Node ArithRewriter::rewriteIneqToBv(const Node& ineq)
{
  Assert(ineq.getKind() == kind::GEQ);

  Node left = rewriter::removeToReal(ineq[0]);
  Node right = rewriter::removeToReal(ineq[1]);

  rewriter::Sum sum;
  rewriter::addToSum(sum, left, false);
  rewriter::addToSum(sum, right, true);

  return rewriteIneqToBv(kind::GEQ, sum, ineq);
}

Node ArithRewriter::rewriteIneqToBv(Kind kind,
                                    const rewriter::Sum& sum,
                                    const Node& ineq)
{
  bool convertible = true;
  // the (single) bv2nat term in the sum
  Node bv2natTerm;
  // whether the bv2nat term is positive in the sum
  bool bv2natPol = false;
  // the remaining sum (constant)
  std::vector<Node> otherSum;
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const Node, RealAlgebraicNumber>& m : sum)
  {
    if (m.second.isRational())
    {
      const Rational& r = m.second.toRational();
      Kind mk = m.first.getKind();
      if (mk == BITVECTOR_TO_NAT)
      {
        // We currently only eliminate sums involving exactly one
        // (bv2nat x) monomial whose coefficient is +- 1, although more
        // cases could be handled here.
        if (bv2natTerm.isNull())
        {
          if (r.abs().isOne())
          {
            bv2natPol = (r.sgn() == 1);
            bv2natTerm = m.first;
            continue;
          }
        }
        else
        {
          convertible = false;
          break;
        }
      }
      else if (mk == CONST_INTEGER && m.second.isRational())
      {
        if (r.isIntegral())
        {
          otherSum.push_back(nm->mkConstInt(r));
          continue;
        }
      }
      // if a non-constant, non-bv2nat term is in the sum, we fail
    }
    convertible = false;
    break;
  }
  if (convertible && !bv2natTerm.isNull())
  {
    Node zero = nm->mkConstInt(Rational(0));
    Kind bvKind = (kind == GT ? (bv2natPol ? BITVECTOR_UGT : BITVECTOR_ULT)
                              : (bv2natPol ? BITVECTOR_UGE : BITVECTOR_ULE));
    Node bvt = bv2natTerm[0];
    size_t bvsize = bvt.getType().getBitVectorSize();
    Node w = nm->mkConstInt(Rational(Integer(2).pow(bvsize)));
    Node osum =
        otherSum.empty()
            ? zero
            : (otherSum.size() == 1 ? otherSum[0] : nm->mkNode(ADD, otherSum));
    Node o = bv2natPol ? nm->mkNode(NEG, osum) : osum;
    Node ub = nm->mkNode(GEQ, o, w);
    Node lb = nm->mkNode(LT, o, zero);
    Node iToBvop = nm->mkConst(IntToBitVector(bvsize));
    Node ret = nm->mkNode(
        ITE,
        ub,
        nm->mkConst(!bv2natPol),
        nm->mkNode(
            ITE,
            lb,
            nm->mkConst(bv2natPol),
            nm->mkNode(bvKind, bvt, nm->mkNode(INT_TO_BITVECTOR, iToBvop, o))));
    // E.g. (<= (bv2nat x) N) -->
    //      (ite (>= N 2^w) true (ite (< N 0) false (bvule x ((_ int2bv w) N))
    // or   (<= N (bv2nat x)) -->
    //      (ite (>= N 2^w) false (ite (< N 0) true (bvuge x ((_ int2bv w) N))
    // where N is a constant. Note that ((_ int2bv w) N) will subsequently
    // be rewritten to the appropriate bitvector constant.
    return ret;
  }
  return ineq;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
