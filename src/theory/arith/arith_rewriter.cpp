/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
#include "expr/node_algorithm.h"
#include "smt/logic_exception.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/operator_elim.h"
#include "theory/arith/rewriter/addition.h"
#include "theory/arith/rewriter/node_utils.h"
#include "theory/arith/rewriter/ordering.h"
#include "theory/arith/rewriter/rewrite_atom.h"
#include "theory/rewriter.h"
#include "theory/strings/arith_entail.h"
#include "theory/theory.h"
#include "util/bitvector.h"
#include "util/divisible.h"
#include "util/iand.h"
#include "util/real_algebraic_number.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {

ArithRewriter::ArithRewriter(NodeManager* nm,
                             OperatorElim& oe,
                             bool expertEnabled)
    : TheoryRewriter(nm), d_opElim(oe), d_expertEnabled(expertEnabled)
{
  registerProofRewriteRule(ProofRewriteRule::ARITH_POW_ELIM,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_ARITH_STRING_PRED_ENTAIL,
                           TheoryRewriteCtx::DSL_SUBCALL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_ARITH_INT_EQ_CONFLICT,
                           TheoryRewriteCtx::DSL_SUBCALL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_ARITH_INT_GEQ_TIGHTEN,
                           TheoryRewriteCtx::DSL_SUBCALL);
  // we don't register ARITH_STRING_PRED_ENTAIL or
  // ARITH_STRING_PRED_SAFE_APPROX, as these are subsumed by
  // MACRO_ARITH_STRING_PRED_ENTAIL.
}

Node ArithRewriter::rewriteViaRule(ProofRewriteRule id, const Node& n)
{
  switch (id)
  {
    case ProofRewriteRule::ARITH_POW_ELIM:
    {
      if (n.getKind() == Kind::POW)
      {
        Node nx = expandPowConst(nodeManager(), n);
        if (!nx.isNull())
        {
          return nx;
        }
      }
    }
    break;
    case ProofRewriteRule::MACRO_ARITH_STRING_PRED_ENTAIL:
    {
      // only matters if n contains integer string operators
      if (!n.getType().isBoolean() || n.getNumChildren() != 2 || n[0] == n[1]
          || !expr::hasSubtermKinds(
              {Kind::STRING_LENGTH, Kind::STRING_INDEXOF, Kind::STRING_STOI},
              n))
      {
        return Node::null();
      }
      Trace("macro-arith-str-pred") << "Check entailment " << n << std::endl;
      // Note that we do *not* pass a rewriter here, since the proof rule
      // cannot depend on the rewriter. This makes this rule capture most
      // but not all cases of this kind of reasoning.
      theory::strings::ArithEntail ae(nullptr);
      Node tgt;
      if (n.getKind() == Kind::EQUAL)
      {
        tgt = n;
      }
      else
      {
        tgt = ae.normalizeGeq(n);
      }
      if (tgt.isNull() || !tgt[0].getType().isInteger())
      {
        return Node::null();
      }
      // first do basic length intro, which rewrites (str.len (str.++ x y))
      // to (+ (str.len x) (str.len y))
      Node nexp = ae.rewriteLengthIntro(tgt);
      Trace("macro-arith-str-pred") << "...setup to " << nexp << std::endl;
      // Also must make this a "simple" check (isSimple = true).
      Node ret = ae.rewritePredViaEntailment(nexp, true);
      Trace("macro-arith-str-pred") << "...result = " << ret << std::endl;
      return ret;
    }
    break;
    case ProofRewriteRule::ARITH_STRING_PRED_ENTAIL:
    case ProofRewriteRule::ARITH_STRING_PRED_SAFE_APPROX:
    {
      if (n.getKind() != Kind::GEQ || !n[1].isConst()
          || n[1].getConst<Rational>().sgn() != 0)
      {
        return Node::null();
      }
      if (id == ProofRewriteRule::ARITH_STRING_PRED_ENTAIL)
      {
        if (theory::strings::ArithEntail::checkSimple(n[0]))
        {
          return nodeManager()->mkConst(true);
        }
      }
      else if (id == ProofRewriteRule::ARITH_STRING_PRED_SAFE_APPROX)
      {
        // Note that we do *not* pass a rewriter here, since the proof rule
        // cannot depend on the rewriter.
        theory::strings::ArithEntail ae(nullptr);
        // must only use simple checks when computing the approximations
        Node approx = ae.findApprox(n[0], true);
        if (approx != n[0])
        {
          Trace("arith-rewriter-proof")
              << n[0] << " --> " << approx << " by safe approx" << std::endl;
          return nodeManager()->mkNode(Kind::GEQ, approx, n[1]);
        }
      }
    }
    break;
    case ProofRewriteRule::MACRO_ARITH_INT_EQ_CONFLICT:
    {
      if (n.getKind() == Kind::EQUAL && n[0] != n[1])
      {
        Node a = n[0].getKind() == Kind::TO_REAL ? n[0][0] : n[0];
        Node b = n[1].getKind() == Kind::TO_REAL ? n[1][0] : n[1];
        rewriter::Sum sum;
        rewriter::addToSum(sum, a, false);
        rewriter::addToSum(sum, b, true);
        if (rewriter::isIntegral(sum))
        {
          std::pair<Node, Node> p = decomposeSum(d_nm, std::move(sum));
          Rational c = p.second.getConst<Rational>();
          if (!c.isIntegral())
          {
            return d_nm->mkConst(false);
          }
        }
      }
    }
    break;
    case ProofRewriteRule::MACRO_ARITH_INT_GEQ_TIGHTEN:
    {
      Trace("arith-rewriter-proof") << "Rewrite " << n << "?" << std::endl;
      if (n.getKind() == Kind::GEQ && n[0] != n[1])
      {
        Node a = n[0].getKind() == Kind::TO_REAL ? n[0][0] : n[0];
        Node b = n[1].getKind() == Kind::TO_REAL ? n[1][0] : n[1];
        rewriter::Sum sum;
        rewriter::addToSum(sum, a, false);
        rewriter::addToSum(sum, b, true);
        if (rewriter::isIntegral(sum))
        {
          // decompose the sum into a non-constant and constant part
          bool negated = false;
          std::pair<Node, Node> p =
              decomposeSum(d_nm, std::move(sum), negated, true);
          Rational c = p.second.getConst<Rational>();
          Trace("arith-rewriter-proof")
              << "Decomposed to " << p.first << " + " << p.second << std::endl;
          if (!c.isIntegral())
          {
            c = -c;
            c = c.ceiling();
            Node ret = d_nm->mkNode(Kind::GEQ, p.first, d_nm->mkConstInt(c));
            if (negated)
            {
              ret = ret.notNode();
            }
            return ret;
          }
        }
      }
    }
    break;
    default: break;
  }
  return Node::null();
}

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
      return RewriteResponse(REWRITE_DONE, rewriter::mkConst(d_nm, *response));
    }
  }

  switch (kind)
  {
    case Kind::GT:
      return RewriteResponse(
          REWRITE_DONE,
          rewriter::buildRelation(Kind::LEQ, atom[0], atom[1], true));
    case Kind::LT:
      return RewriteResponse(
          REWRITE_DONE,
          rewriter::buildRelation(Kind::GEQ, atom[0], atom[1], true));
    case Kind::IS_INTEGER:
      if (atom[0].getType().isInteger())
      {
        return RewriteResponse(REWRITE_DONE, rewriter::mkConst(d_nm, true));
      }
      break;
    case Kind::DIVISIBLE:
      if (atom.getOperator().getConst<Divisible>().k.isOne())
      {
        return RewriteResponse(REWRITE_DONE, rewriter::mkConst(d_nm, true));
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

  if (atom.getKind() == Kind::IS_INTEGER)
  {
    return rewriteExtIntegerOp(atom);
  }
  else if (atom.getKind() == Kind::DIVISIBLE)
  {
    const Integer& k = atom.getOperator().getConst<Divisible>().k;
    if (atom[0].isConst())
    {
      const Rational& num = atom[0].getConst<Rational>();
      return RewriteResponse(REWRITE_DONE,
                             rewriter::mkConst(d_nm, (num / k).isIntegral()));
    }
    if (k.isOne())
    {
      return RewriteResponse(REWRITE_DONE, rewriter::mkConst(d_nm, true));
    }
    NodeManager* nm = nodeManager();
    return RewriteResponse(REWRITE_AGAIN,
                           nm->mkNode(Kind::EQUAL,
                                      nm->mkNode(Kind::INTS_MODULUS_TOTAL,
                                                 atom[0],
                                                 rewriter::mkConst(d_nm, k)),
                                      rewriter::mkConst(d_nm, Integer(0))));
  }
  // left |><| right
  Kind kind = atom.getKind();
  Node left = rewriter::removeToReal(atom[0]);
  Node right = rewriter::removeToReal(atom[1]);

  if (auto response = rewriter::tryEvaluateRelationReflexive(kind, left, right);
      response)
  {
    return RewriteResponse(REWRITE_DONE, rewriter::mkConst(d_nm, *response));
  }

  Assert(isRelationOperator(kind));

  if (auto response = rewriter::tryEvaluateRelation(kind, left, right);
      response)
  {
    return RewriteResponse(REWRITE_DONE, rewriter::mkConst(d_nm, *response));
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
      return RewriteResponse(
          REWRITE_DONE, rewriter::buildIntegerEquality(d_nm, std::move(sum)));
    }
    return RewriteResponse(
        REWRITE_DONE,
        rewriter::buildIntegerInequality(d_nm, std::move(sum), kind));
  }
  else
  {
    if (kind == Kind::EQUAL)
    {
      return RewriteResponse(REWRITE_DONE,
                             rewriter::buildRealEquality(d_nm, std::move(sum)));
    }
    return RewriteResponse(
        REWRITE_DONE,
        rewriter::buildRealInequality(d_nm, std::move(sum), kind));
  }
}

RewriteResponse ArithRewriter::preRewriteTerm(TNode t){
  if(t.isConst()){
    return RewriteResponse(REWRITE_DONE, t);
  }else if(t.isVar()){
    return rewriteVariable(t);
  }else{
    switch(Kind k = t.getKind()){
      case Kind::REAL_ALGEBRAIC_NUMBER: return rewriteRAN(t);
      case Kind::SUB: return rewriteSub(t);
      case Kind::NEG: return rewriteNeg(t, true);
      case Kind::DIVISION:
      case Kind::DIVISION_TOTAL: return rewriteDiv(t, true);
      case Kind::ADD: return preRewritePlus(t);
      case Kind::MULT:
      case Kind::NONLINEAR_MULT: return preRewriteMult(t);
      case Kind::IAND: return RewriteResponse(REWRITE_DONE, t);
      case Kind::POW2: return RewriteResponse(REWRITE_DONE, t);
      case Kind::INTS_ISPOW2: return RewriteResponse(REWRITE_DONE, t);
      case Kind::INTS_LOG2: return RewriteResponse(REWRITE_DONE, t);
      case Kind::INTS_DIVISION:
      case Kind::INTS_MODULUS: return rewriteIntsDivMod(t, true);
      case Kind::INTS_DIVISION_TOTAL:
      case Kind::INTS_MODULUS_TOTAL: return rewriteIntsDivModTotal(t, true);
      case Kind::ABS: return rewriteAbs(t);
      case Kind::EXPONENTIAL:
      case Kind::SINE:
      case Kind::COSINE:
      case Kind::TANGENT:
      case Kind::COSECANT:
      case Kind::SECANT:
      case Kind::COTANGENT:
      case Kind::ARCSINE:
      case Kind::ARCCOSINE:
      case Kind::ARCTANGENT:
      case Kind::ARCCOSECANT:
      case Kind::ARCSECANT:
      case Kind::ARCCOTANGENT:
      case Kind::SQRT:
      case Kind::IS_INTEGER:
      case Kind::TO_INTEGER:
      case Kind::TO_REAL:
      case Kind::POW:
      case Kind::PI: return RewriteResponse(REWRITE_DONE, t);
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
      case Kind::REAL_ALGEBRAIC_NUMBER: return rewriteRAN(t);
      case Kind::SUB: return rewriteSub(t);
      case Kind::NEG: return rewriteNeg(t, false);
      case Kind::DIVISION:
      case Kind::DIVISION_TOTAL: return rewriteDiv(t, false);
      case Kind::ADD: return postRewritePlus(t);
      case Kind::MULT:
      case Kind::NONLINEAR_MULT: return postRewriteMult(t);
      case Kind::INTS_ISPOW2: return postRewriteIntsIsPow2(t);
      case Kind::INTS_LOG2: return postRewriteIntsLog2(t);
      case Kind::INTS_DIVISION:
      case Kind::INTS_MODULUS: return rewriteIntsDivMod(t, false);
      case Kind::INTS_DIVISION_TOTAL:
      case Kind::INTS_MODULUS_TOTAL: return rewriteIntsDivModTotal(t, false);
      case Kind::ABS: return rewriteAbs(t);
      case Kind::TO_REAL: return rewriteToReal(t);
      case Kind::TO_INTEGER: return rewriteExtIntegerOp(t);
      case Kind::POW:
      {
        Node tx = expandPowConst(nodeManager(), t);
        if (!tx.isNull())
        {
          return RewriteResponse(REWRITE_AGAIN_FULL, tx);
        }
        return RewriteResponse(REWRITE_DONE, t);
      }
      case Kind::PI: return RewriteResponse(REWRITE_DONE, t);
      // expert cases
      case Kind::EXPONENTIAL:
      case Kind::SINE:
      case Kind::COSINE:
      case Kind::TANGENT:
      case Kind::COSECANT:
      case Kind::SECANT:
      case Kind::COTANGENT:
      case Kind::ARCSINE:
      case Kind::ARCCOSINE:
      case Kind::ARCTANGENT:
      case Kind::ARCCOSECANT:
      case Kind::ARCSECANT:
      case Kind::ARCCOTANGENT:
      case Kind::SQRT:
      case Kind::IAND:
      case Kind::POW2: return postRewriteExpert(t);
      default: Unreachable();
    }
  }
}
RewriteResponse ArithRewriter::postRewriteExpert(TNode t)
{
  if (!d_expertEnabled)
  {
    return RewriteResponse(REWRITE_DONE, t);
  }
  switch (t.getKind())
  {
    case Kind::EXPONENTIAL:
    case Kind::SINE:
    case Kind::COSINE:
    case Kind::TANGENT:
    case Kind::COSECANT:
    case Kind::SECANT:
    case Kind::COTANGENT:
    case Kind::ARCSINE:
    case Kind::ARCCOSINE:
    case Kind::ARCTANGENT:
    case Kind::ARCCOSECANT:
    case Kind::ARCSECANT:
    case Kind::ARCCOTANGENT:
    case Kind::SQRT: return postRewriteTranscendental(t);
    case Kind::IAND: return postRewriteIAnd(t);
    case Kind::POW2: return postRewritePow2(t);
    default: Unreachable();
  }
}

RewriteResponse ArithRewriter::rewriteRAN(TNode t)
{
  Assert(rewriter::isRAN(t));
  Assert(t.getType().isReal());
  const RealAlgebraicNumber& r = rewriter::getRAN(t);
  if (r.isRational())
  {
    return RewriteResponse(REWRITE_DONE,
                           rewriter::mkConst(d_nm, r.toRational()));
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
  Assert(t.getKind() == Kind::NEG);

  NodeManager* nm = nodeManager();
  if (t[0].isConst())
  {
    Rational neg = -(t[0].getConst<Rational>());
    return RewriteResponse(REWRITE_DONE,
                           nm->mkConstRealOrInt(t.getType(), neg));
  }
  if (rewriter::isRAN(t[0]))
  {
    return RewriteResponse(REWRITE_DONE,
                           rewriter::mkConst(d_nm, -rewriter::getRAN(t[0])));
  }

  Node noUminus =
      nm->mkNode(Kind::MULT, rewriter::mkConst(d_nm, Rational(-1)), t[0]);
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
  Assert(t.getKind() == Kind::SUB);
  Assert(t.getNumChildren() == 2);

  NodeManager* nm = nodeManager();
  if (t[0] == t[1])
  {
    return RewriteResponse(REWRITE_DONE,
                           nm->mkConstRealOrInt(t.getType(), Rational(0)));
  }
  return RewriteResponse(
      REWRITE_AGAIN_FULL,
      nm->mkNode(Kind::ADD,
                 t[0],
                 nm->mkNode(Kind::MULT,
                            nm->mkConstRealOrInt(t[1].getType(), Rational(-1)),
                            t[1])));
}

RewriteResponse ArithRewriter::preRewritePlus(TNode t)
{
  Assert(t.getKind() == Kind::ADD);
  return RewriteResponse(REWRITE_DONE, expr::algorithm::flatten(d_nm, t));
}

RewriteResponse ArithRewriter::postRewritePlus(TNode t)
{
  Assert(t.getKind() == Kind::ADD);
  Assert(t.getNumChildren() > 1);

  std::vector<TNode> children;
  expr::algorithm::flatten(t, children, Kind::ADD, Kind::TO_REAL);

  rewriter::Sum sum;
  for (const auto& child : children)
  {
    rewriter::addToSum(sum, child);
  }
  Node retSum = rewriter::collectSum(d_nm, sum);
  retSum = rewriter::maybeEnsureReal(t.getType(), retSum);
  return RewriteResponse(REWRITE_DONE, retSum);
}

RewriteResponse ArithRewriter::preRewriteMult(TNode node)
{
  Assert(node.getKind() == Kind::MULT
         || node.getKind() == Kind::NONLINEAR_MULT);

  if (auto res = rewriter::getZeroChild(node); res)
  {
    return RewriteResponse(REWRITE_DONE,
                           rewriter::maybeEnsureReal(node.getType(), *res));
  }
  return RewriteResponse(REWRITE_DONE, node);
}

RewriteResponse ArithRewriter::postRewriteMult(TNode t){
  Assert(t.getKind() == Kind::MULT || t.getKind() == Kind::NONLINEAR_MULT);
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
    ret = rewriter::distributeMultiplication(d_nm, children);
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
    ret = rewriter::mkMultTerm(d_nm, ran, std::move(leafs));
  }
  ret = rewriter::maybeEnsureReal(t.getType(), ret);
  return RewriteResponse(REWRITE_DONE, ret);
}

RewriteResponse ArithRewriter::rewriteDiv(TNode t, bool pre)
{
  Assert(t.getKind() == Kind::DIVISION_TOTAL || t.getKind() == Kind::DIVISION);
  Assert(t.getNumChildren() == 2);

  Node left = rewriter::removeToReal(t[0]);
  Node right = rewriter::removeToReal(t[1]);
  NodeManager* nm = nodeManager();
  if (right.isConst())
  {
    const Rational& den = right.getConst<Rational>();

    if (den.isZero())
    {
      if (t.getKind() == Kind::DIVISION_TOTAL)
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
    Node mult =
        rewriter::ensureReal(nodeManager()->mkNode(Kind::MULT, left, result));
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
              d_nm, RealAlgebraicNumber(left.getConst<Rational>()) / den)));
    }
    if (rewriter::isRAN(left))
    {
      return RewriteResponse(REWRITE_DONE,
                             rewriter::ensureReal(rewriter::mkConst(
                                 d_nm, rewriter::getRAN(left) / den)));
    }

    Node result = rewriter::mkConst(d_nm, den.inverse());
    Node mult =
        rewriter::ensureReal(nodeManager()->mkNode(Kind::MULT, left, result));
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
  Assert(t.getKind() == Kind::TO_REAL);
  if (!t[0].getType().isInteger())
  {
    // if it is already real type, then just return the argument
    return RewriteResponse(REWRITE_DONE, t[0]);
  }
  NodeManager* nm = nodeManager();
  if (t[0].isConst())
  {
    // If the argument is constant, return a real constant.
    const Rational& rat = t[0].getConst<Rational>();
    return RewriteResponse(REWRITE_DONE, nm->mkConstReal(rat));
  }
  if (t[0].getKind() == Kind::TO_REAL)
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
        REWRITE_DONE, nodeManager()->mkConstRealOrInt(t[0].getType(), -rat));
  }
  if (rewriter::isRAN(t[0]))
  {
    const RealAlgebraicNumber& ran = rewriter::getRAN(t[0]);
    if (ran >= RealAlgebraicNumber())
    {
      return RewriteResponse(REWRITE_DONE, t[0]);
    }
    return RewriteResponse(REWRITE_DONE,
                           nodeManager()->mkRealAlgebraicNumber(-ran));
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteIntsDivMod(TNode t, bool pre)
{
  NodeManager* nm = nodeManager();
  Kind k = t.getKind();
  if (k == Kind::INTS_MODULUS)
  {
    if (t[1].isConst() && !t[1].getConst<Rational>().isZero())
    {
      // can immediately replace by INTS_MODULUS_TOTAL
      Node ret = nm->mkNode(Kind::INTS_MODULUS_TOTAL, t[0], t[1]);
      return returnRewrite(t, ret, Rewrite::MOD_TOTAL_BY_CONST);
    }
  }
  if (k == Kind::INTS_DIVISION)
  {
    if (t[1].isConst() && !t[1].getConst<Rational>().isZero())
    {
      // can immediately replace by INTS_DIVISION_TOTAL
      Node ret = nm->mkNode(Kind::INTS_DIVISION_TOTAL, t[0], t[1]);
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
  NodeManager* nm = nodeManager();
  Kind k = t.getKind();
  Assert(k == Kind::INTS_MODULUS_TOTAL || k == Kind::INTS_DIVISION_TOTAL);
  TNode n = t[0];
  TNode d = t[1];
  bool dIsConstant = d.isConst();
  if (dIsConstant && d.getConst<Rational>().isZero())
  {
    // (div_total x 0) ---> 0 or (mod_total x 0) ---> x
    Node ret = k == Kind::INTS_MODULUS_TOTAL ? Node(t[0]) : nm->mkConstInt(0);
    return returnRewrite(t, ret, Rewrite::DIV_MOD_BY_ZERO);
  }
  else if (dIsConstant && d.getConst<Rational>().isOne())
  {
    if (k == Kind::INTS_MODULUS_TOTAL)
    {
      // (mod_total x 1) --> 0
      return returnRewrite(t, nm->mkConstInt(0), Rewrite::MOD_BY_ONE);
    }
    Assert(k == Kind::INTS_DIVISION_TOTAL);
    // (div_total x 1) --> x
    return returnRewrite(t, n, Rewrite::DIV_BY_ONE);
  }
  else if (dIsConstant && d.getConst<Rational>().sgn() < 0)
  {
    // pull negation
    // (div_total x (- c)) ---> (- (div_total x c))
    // (mod_total x (- c)) ---> (mod_total x c)
    Node nn = nm->mkNode(k, t[0], nm->mkConstInt(-t[1].getConst<Rational>()));
    Node ret = k == Kind::INTS_DIVISION_TOTAL
                   ? nm->mkNode(Kind::NEG, nn)
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

    bool isDiv = (k == Kind::INTS_DIVISION_TOTAL);

    Integer result = isDiv ? ni.euclidianDivideQuotient(di)
                           : ni.euclidianDivideRemainder(di);

    // constant evaluation
    // (mod_total c1 c2) ---> c3 or (div_total c1 c2) ---> c3
    Node resultNode = nm->mkConstInt(Rational(result));
    return returnRewrite(t, resultNode, Rewrite::CONST_EVAL);
  }
  if (k == Kind::INTS_MODULUS_TOTAL)
  {
    // Note these rewrites do not need to account for modulus by zero as being
    // a UF, which is handled by the reduction of INTS_MODULUS.
    Kind k0 = t[0].getKind();
    if (k0 == Kind::INTS_MODULUS_TOTAL && t[0][1] == t[1])
    {
      // (mod_total (mod_total x c) c) --> (mod x c)
      return returnRewrite(t, t[0], Rewrite::MOD_OVER_MOD);
    }
    else if (k0 == Kind::NONLINEAR_MULT || k0 == Kind::MULT || k0 == Kind::ADD)
    {
      // can drop all
      std::vector<Node> newChildren;
      bool childChanged = false;
      for (const Node& tc : t[0])
      {
        if (tc.getKind() == Kind::INTS_MODULUS_TOTAL && tc[1] == t[1])
        {
          newChildren.push_back(tc[0]);
          childChanged = true;
          continue;
        }
        newChildren.push_back(tc);
      }
      if (childChanged)
      {
        // (mod_total (op ... (mod_total x c) ...) c) ---> 
        // (mod_total (op ... x ...) c) where
        // op is one of { NONLINEAR_MULT, MULT, ADD }.
        Node ret = nm->mkNode(k0, newChildren);
        ret = nm->mkNode(Kind::INTS_MODULUS_TOTAL, ret, t[1]);
        return returnRewrite(t, ret, Rewrite::MOD_CHILD_MOD);
      }
    }
  }
  else
  {
    Assert(k == Kind::INTS_DIVISION_TOTAL);
    // Note these rewrites do not need to account for division by zero as being
    // a UF, which is handled by the reduction of INTS_DIVISION.
    if (t[0].getKind() == Kind::INTS_MODULUS_TOTAL && t[0][1] == t[1])
    {
      // (div_total (mod_total x c) c) --> 0
      Node ret = nm->mkConstInt(0);
      return returnRewrite(t, ret, Rewrite::DIV_OVER_MOD);
    }
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteExtIntegerOp(TNode t)
{
  Assert(t.getKind() == Kind::TO_INTEGER || t.getKind() == Kind::IS_INTEGER);
  bool isPred = t.getKind() == Kind::IS_INTEGER;
  NodeManager* nm = nodeManager();
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
  if (t[0].getKind() == Kind::TO_REAL)
  {
    Node ret = nm->mkNode(t.getKind(), t[0][0]);
    return returnRewrite(t, ret, Rewrite::INT_EXT_TO_REAL);
  }
  if (d_expertEnabled)
  {
    if (t[0].getKind() == Kind::PI)
    {
      Node ret = isPred ? nm->mkConst(false) : nm->mkConstInt(Rational(3));
      return returnRewrite(t, ret, Rewrite::INT_EXT_PI);
    }
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteIAnd(TNode t)
{
  Assert(t.getKind() == Kind::IAND);
  uint32_t bsize = t.getOperator().getConst<IntAnd>().d_size;
  NodeManager* nm = nodeManager();
  // if constant, we eliminate
  if (t[0].isConst() && t[1].isConst())
  {
    Node iToBvop = nm->mkConst(IntToBitVector(bsize));
    Node arg1 = nm->mkNode(Kind::INT_TO_BITVECTOR, iToBvop, t[0]);
    Node arg2 = nm->mkNode(Kind::INT_TO_BITVECTOR, iToBvop, t[1]);
    Node bvand = nm->mkNode(Kind::BITVECTOR_AND, arg1, arg2);
    Node ret = nm->mkNode(Kind::BITVECTOR_TO_NAT, bvand);
    return RewriteResponse(REWRITE_AGAIN_FULL, ret);
  }
  else if (t[0] > t[1])
  {
    // ((_ iand k) x y) ---> ((_ iand k) y x) if x > y by node ordering
    Node ret = nm->mkNode(Kind::IAND, t.getOperator(), t[1], t[0]);
    return RewriteResponse(REWRITE_AGAIN, ret);
  }
  else if (t[0] == t[1])
  {
    // ((_ iand k) x x) ---> (mod x 2^k)
    Node twok = nm->mkConstInt(Rational(Integer(2).pow(bsize)));
    Node ret = nm->mkNode(Kind::INTS_MODULUS, t[0], twok);
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
      Node ret = nm->mkNode(Kind::INTS_MODULUS, t[1 - i], twok);
      return RewriteResponse(REWRITE_AGAIN, ret);
    }
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewritePow2(TNode t)
{
  Assert(t.getKind() == Kind::POW2);
  NodeManager* nm = nodeManager();
  // if constant, we eliminate
  if (t[0].isConst())
  {
    // pow2 is only supported for integers
    Assert(t[0].getType().isInteger());
    Integer i = t[0].getConst<Rational>().getNumerator();
    if (i < 0)
    {
      return RewriteResponse(REWRITE_DONE, rewriter::mkConst(d_nm, Integer(0)));
    }
    // (pow2 t) ---> (pow 2 t) and continue rewriting to eliminate pow
    Node two = rewriter::mkConst(d_nm, Integer(2));
    Node ret = nm->mkNode(Kind::POW, two, t[0]);
    return RewriteResponse(REWRITE_AGAIN, ret);
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteIntsIsPow2(TNode t)
{
  Assert(t.getKind() == Kind::INTS_ISPOW2);
  // if constant, we eliminate
  if (t[0].isConst())
  {
    // pow2 is only supported for integers
    Assert(t[0].getType().isInteger());
    Integer i = t[0].getConst<Rational>().getNumerator();

    return RewriteResponse(REWRITE_DONE, rewriter::mkConst(d_nm, i.isPow2()));
  }
  return RewriteResponse(REWRITE_DONE, t);
}
RewriteResponse ArithRewriter::postRewriteIntsLog2(TNode t)
{
  Assert(t.getKind() == Kind::INTS_LOG2);
  // if constant, we eliminate
  if (t[0].isConst())
  {
    // pow2 is only supported for integers
    Assert(t[0].getType().isInteger());
    const Rational& r = t[0].getConst<Rational>();
    if (r.sgn() < 0)
    {
      return RewriteResponse(REWRITE_DONE, rewriter::mkConst(d_nm, Integer(0)));
    }
    Integer i = r.getNumerator();
    size_t const length = i.length();
    return RewriteResponse(REWRITE_DONE,
                           rewriter::mkConst(d_nm, Integer(length - 1)));
  }
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteTranscendental(TNode t)
{
  Trace("arith-tf-rewrite")
      << "Rewrite transcendental function : " << t << std::endl;
  Assert(t.getTypeOrNull(true).isReal());
  NodeManager* nm = nodeManager();
  switch (t.getKind())
  {
    case Kind::EXPONENTIAL:
    {
      if (t[0].isConst())
      {
        Rational r = t[0].getConst<Rational>();
        if (r.sgn() == 0)
        {
          Node one = nm->mkConstReal(Rational(1));
          // (= (exp 0.0) 1.0)
          return RewriteResponse(REWRITE_DONE, one);
        }
        else
        {
          return RewriteResponse(REWRITE_DONE, t);
        }
      }
      else if (t[0].getKind() == Kind::ADD)
      {
        std::vector<Node> product;
        for (const Node tc : t[0])
        {
          Node tcr = rewriter::ensureReal(tc);
          product.push_back(nm->mkNode(Kind::EXPONENTIAL, tcr));
        }
        // We need to do a full rewrite here, since we can get exponentials of
        // constants, e.g. when we are rewriting exp(2 + x)
        return RewriteResponse(REWRITE_AGAIN_FULL,
                               nm->mkNode(Kind::MULT, product));
      }
    }
    break;
    case Kind::SINE:
      if (t[0].isConst())
      {
        const Rational& rat = t[0].getConst<Rational>();
        if (rat.sgn() == 0)
        {
          return RewriteResponse(REWRITE_DONE, nm->mkConstReal(Rational(0)));
        }
        else if (rat.sgn() == -1)
        {
          Node ret = nm->mkNode(Kind::NEG,
                                nm->mkNode(Kind::SINE, nm->mkConstReal(-rat)));
          return RewriteResponse(REWRITE_AGAIN_FULL, ret);
        }
      }
      else if ((t[0].getKind() == Kind::MULT
                || t[0].getKind() == Kind::NONLINEAR_MULT)
               && t[0][0].isConst() && t[0][0].getConst<Rational>().sgn() == -1)
      {
        // sin(-n*x) ---> -sin(n*x)
        std::vector<Node> mchildren(t[0].begin(), t[0].end());
        mchildren[0] = nm->mkConstReal(-t[0][0].getConst<Rational>());
        Node ret = nm->mkNode(
            Kind::NEG,
            nm->mkNode(Kind::SINE, nm->mkNode(t[0].getKind(), mchildren)));
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
          pi = mkPi(nm);
          std::map<Node, Node>::iterator itm = msum.find(pi);
          if (itm != msum.end())
          {
            if (itm->second.isNull())
            {
              pi_factor = rewriter::mkConst(d_nm, Integer(1));
            }
            else
            {
              pi_factor = itm->second;
            }
            msum.erase(pi);
            if (!msum.empty())
            {
              rem = ArithMSum::mkNode(nm, msum);
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
            Node new_arg = nm->mkNode(Kind::MULT, new_pi_factor, pi);
            if (!rem.isNull())
            {
              new_arg = nm->mkNode(Kind::ADD, new_arg, rem);
            }
            new_arg = rewriter::ensureReal(new_arg);
            // sin( 2*n*PI + x ) = sin( x )
            return RewriteResponse(REWRITE_AGAIN_FULL,
                                   nm->mkNode(Kind::SINE, new_arg));
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
              rem = rewriter::ensureReal(rem);
              return RewriteResponse(
                  REWRITE_AGAIN_FULL,
                  nm->mkNode(Kind::NEG, nm->mkNode(Kind::SINE, rem)));
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
    case Kind::COSINE:
    {
      return RewriteResponse(
          REWRITE_AGAIN_FULL,
          nm->mkNode(
              Kind::SINE,
              nm->mkNode(Kind::SUB,
                         nm->mkNode(Kind::MULT,
                                    nm->mkConstReal(Rational(1) / Rational(2)),
                                    mkPi(nm)),
                         t[0])));
    }
    break;
    case Kind::TANGENT:
    {
      return RewriteResponse(REWRITE_AGAIN_FULL,
                             nm->mkNode(Kind::DIVISION,
                                        nm->mkNode(Kind::SINE, t[0]),
                                        nm->mkNode(Kind::COSINE, t[0])));
    }
    break;
    case Kind::COSECANT:
    {
      return RewriteResponse(REWRITE_AGAIN_FULL,
                             nm->mkNode(Kind::DIVISION,
                                        nm->mkConstReal(Rational(1)),
                                        nm->mkNode(Kind::SINE, t[0])));
    }
    break;
    case Kind::SECANT:
    {
      return RewriteResponse(REWRITE_AGAIN_FULL,
                             nm->mkNode(Kind::DIVISION,
                                        nm->mkConstReal(Rational(1)),
                                        nm->mkNode(Kind::COSINE, t[0])));
    }
    break;
    case Kind::COTANGENT:
    {
      return RewriteResponse(REWRITE_AGAIN_FULL,
                             nm->mkNode(Kind::DIVISION,
                                        nm->mkNode(Kind::COSINE, t[0]),
                                        nm->mkNode(Kind::SINE, t[0])));
    }
    break;
    default: break;
  }
  return RewriteResponse(REWRITE_DONE, t);
}

Node ArithRewriter::expandDefinition(Node node)
{
  // call eliminate operators, to eliminate partial operators only
  std::vector<SkolemLemma> lems;
  TrustNode ret = d_opElim.eliminate(node, lems, true);
  Assert(lems.empty());
  if (ret.isNull())
  {
    return Node::null();
  }
  return ret.getNode();
}

RewriteResponse ArithRewriter::returnRewrite(TNode t, Node ret, Rewrite r)
{
  Trace("arith-rewriter") << "ArithRewriter : " << t << " == " << ret << " by "
                          << r << std::endl;
  return RewriteResponse(REWRITE_AGAIN_FULL, ret);
}

Node ArithRewriter::rewriteIneqToBv(const Node& ineq)
{
  Assert(ineq.getKind() == Kind::GEQ);

  Node left = rewriter::removeToReal(ineq[0]);
  Node right = rewriter::removeToReal(ineq[1]);

  rewriter::Sum sum;
  rewriter::addToSum(sum, left, false);
  rewriter::addToSum(sum, right, true);

  return rewriteIneqToBv(Kind::GEQ, sum, ineq);
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
  NodeManager* nm = nodeManager();
  for (const std::pair<const Node, RealAlgebraicNumber>& m : sum)
  {
    if (m.second.isRational())
    {
      const Rational& r = m.second.toRational();
      Kind mk = m.first.getKind();
      if (mk == Kind::BITVECTOR_TO_NAT)
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
      else if (mk == Kind::CONST_INTEGER && m.second.isRational())
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
    Kind bvKind =
        (kind == Kind::GT
             ? (bv2natPol ? Kind::BITVECTOR_UGT : Kind::BITVECTOR_ULT)
             : (bv2natPol ? Kind::BITVECTOR_UGE : Kind::BITVECTOR_ULE));
    Node bvt = bv2natTerm[0];
    size_t bvsize = bvt.getType().getBitVectorSize();
    Node w = nm->mkConstInt(Rational(Integer(2).pow(bvsize)));
    Node osum = otherSum.empty()
                    ? zero
                    : (otherSum.size() == 1 ? otherSum[0]
                                            : nm->mkNode(Kind::ADD, otherSum));
    // possibly negate the sum
    Node o = bv2natPol
                 ? (osum.getKind() == Kind::NEG ? osum[0]
                                                : nm->mkNode(Kind::NEG, osum))
                 : osum;
    Node ub = nm->mkNode(Kind::GEQ, o, w);
    Node lb = nm->mkNode(Kind::LT, o, zero);
    Node iToBvop = nm->mkConst(IntToBitVector(bvsize));
    Node ret = nm->mkNode(
        Kind::ITE,
        ub,
        nm->mkConst(!bv2natPol),
        nm->mkNode(
            Kind::ITE,
            lb,
            nm->mkConst(bv2natPol),
            nm->mkNode(
                bvKind, bvt, nm->mkNode(Kind::INT_TO_BITVECTOR, iToBvop, o))));
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

Node ArithRewriter::expandPowConst(NodeManager* nm, const Node& t)
{
  if (t[1].isConst())
  {
    const Rational& exp = t[1].getConst<Rational>();
    if (!exp.isIntegral())
    {
      return Node::null();
    }
    TNode base = t[0];
    if (exp.sgn() == 0)
    {
      return nm->mkConstRealOrInt(t.getType(), Rational(1));
    }
    else if (exp.sgn() > 0)
    {
      Rational r(expr::NodeValue::MAX_CHILDREN);
      if (exp <= r)
      {
        unsigned num = exp.getNumerator().toUnsignedInt();
        Node ret;
        if (num == 1)
        {
          ret = base;
        }
        else
        {
          NodeBuilder nb(nm, Kind::MULT);
          for (unsigned i = 0; i < num; ++i)
          {
            nb << base;
          }
          Assert(nb.getNumChildren() > 0);
          ret = nb;
        }
        return ret;
      }
    }
  }
  return Node::null();
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
