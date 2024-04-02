/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of operator elimination for arithmetic.
 */

#include "theory/arith/operator_elim.h"

#include <sstream>

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "options/arith_options.h"
#include "proof/conv_proof_generator.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/nl/poly_conversion.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {

/**
 * A bound variable for the witness term used to eliminate real algebraic
 * numbers.
 */
struct RealAlgebraicNumberVarAttributeId
{
};
typedef expr::Attribute<RealAlgebraicNumberVarAttributeId, Node>
    RealAlgebraicNumberVarAttribute;
/**
 * A bound variable used for transcendental function purification.
 */
struct TrPurifyAttributeId
{
};
using TrPurifyAttribute = expr::Attribute<TrPurifyAttributeId, Node>;

OperatorElim::OperatorElim(Env& env) : EagerProofGenerator(env) {}

void OperatorElim::checkNonLinearLogic(Node term)
{
  if (d_env.getLogicInfo().isLinear())
  {
    Trace("arith-logic") << "ERROR: Non-linear term in linear logic: " << term
                         << std::endl;
    std::stringstream serr;
    serr << "A non-linear fact was asserted to arithmetic in a linear logic."
         << std::endl;
    serr << "The fact in question: " << term << std::endl;
    throw LogicException(serr.str());
  }
}

TrustNode OperatorElim::eliminate(Node n,
                                  std::vector<SkolemLemma>& lems,
                                  bool partialOnly)
{
  TConvProofGenerator* tg = nullptr;
  Node nn = eliminateOperators(n, lems, tg, partialOnly);
  if (nn != n)
  {
    return TrustNode::mkTrustRewrite(n, nn, nullptr);
  }
  return TrustNode::null();
}

Node OperatorElim::eliminateOperators(Node node,
                                      std::vector<SkolemLemma>& lems,
                                      TConvProofGenerator* tg,
                                      bool partialOnly)
{
  NodeManager* nm = nodeManager();
  SkolemManager* sm = nm->getSkolemManager();
  Kind k = node.getKind();
  switch (k)
  {
    case Kind::TANGENT:
    case Kind::COSECANT:
    case Kind::SECANT:
    case Kind::COTANGENT:
    {
      // these are eliminated by rewriting
      return rewrite(node);
      break;
    }
    case Kind::TO_INTEGER:
    case Kind::IS_INTEGER:
    {
      if (partialOnly)
      {
        // not eliminating total operators
        return node;
      }
      // node[0] - 1 < toIntSkolem <= node[0]
      // -1 < toIntSkolem - node[0] <= 0
      // 0 <= node[0] - toIntSkolem < 1
      Node pterm = nm->mkNode(Kind::TO_INTEGER, node[0]);
      Node v = sm->mkPurifySkolem(pterm);
      Node one = nm->mkConstReal(Rational(1));
      Node zero = nm->mkConstReal(Rational(0));
      Node diff = nm->mkNode(Kind::SUB, node[0], v);
      Node lem = mkInRange(diff, zero, one);
      lems.push_back(mkSkolemLemma(lem, v));
      if (k == Kind::IS_INTEGER)
      {
        return mkEquality(node[0], v);
      }
      Assert(k == Kind::TO_INTEGER);
      return v;
    }

    case Kind::INTS_DIVISION_TOTAL:
    case Kind::INTS_MODULUS_TOTAL:
    {
      if (partialOnly)
      {
        // not eliminating total operators
        return node;
      }
      Node den = rewrite(node[1]);
      Node num = rewrite(node[0]);
      Node rw = nm->mkNode(k, num, den);
      // we use the purification skolem for div
      Node pterm = nm->mkNode(Kind::INTS_DIVISION_TOTAL, node[0], node[1]);
      Node v = sm->mkPurifySkolem(pterm);
      // make the corresponding lemma
      Node lem;
      Node leqNum = nm->mkNode(Kind::LEQ, nm->mkNode(Kind::MULT, den, v), num);
      if (den.isConst())
      {
        const Rational& rat = den.getConst<Rational>();
        if (num.isConst() || rat == 0)
        {
          // just rewrite
          return rewrite(node);
        }
        if (rat > 0)
        {
          lem = nm->mkNode(
              Kind::AND,
              leqNum,
              nm->mkNode(
                  Kind::LT,
                  num,
                  nm->mkNode(
                      Kind::MULT,
                      den,
                      nm->mkNode(Kind::ADD, v, nm->mkConstInt(Rational(1))))));
        }
        else
        {
          lem = nm->mkNode(
              Kind::AND,
              leqNum,
              nm->mkNode(
                  Kind::LT,
                  num,
                  nm->mkNode(
                      Kind::MULT,
                      den,
                      nm->mkNode(Kind::ADD, v, nm->mkConstInt(Rational(-1))))));
        }
      }
      else
      {
        checkNonLinearLogic(node);
        lem = nm->mkNode(
            Kind::AND,
            nm->mkNode(
                Kind::IMPLIES,
                nm->mkNode(Kind::GT, den, nm->mkConstInt(Rational(0))),
                nm->mkNode(
                    Kind::AND,
                    leqNum,
                    nm->mkNode(
                        Kind::LT,
                        num,
                        nm->mkNode(
                            Kind::MULT,
                            den,
                            nm->mkNode(
                                Kind::ADD, v, nm->mkConstInt(Rational(1))))))),
            nm->mkNode(
                Kind::IMPLIES,
                nm->mkNode(Kind::LT, den, nm->mkConstInt(Rational(0))),
                nm->mkNode(
                    Kind::AND,
                    leqNum,
                    nm->mkNode(
                        Kind::LT,
                        num,
                        nm->mkNode(
                            Kind::MULT,
                            den,
                            nm->mkNode(Kind::ADD,
                                       v,
                                       nm->mkConstInt(Rational(-1))))))));
      }
      // add the skolem lemma to lems
      lems.push_back(mkSkolemLemma(lem, v));
      if (k == Kind::INTS_MODULUS_TOTAL)
      {
        Node nn = nm->mkNode(Kind::SUB, num, nm->mkNode(Kind::MULT, den, v));
        return nn;
      }
      return v;
    }
    case Kind::DIVISION_TOTAL:
    {
      if (partialOnly)
      {
        // not eliminating total operators
        return node;
      }
      Node num = rewrite(node[0]);
      Node den = rewrite(node[1]);
      if (den.isConst())
      {
        // No need to eliminate here, can eliminate via rewriting later.
        // Moreover, rewriting may change the type of this node from real to
        // int, which impacts certain issues with subtyping.
        return node;
      }
      checkNonLinearLogic(node);
      Node rw = nm->mkNode(k, num, den);
      Node v = sm->mkPurifySkolem(rw);
      Node lem = nm->mkNode(Kind::IMPLIES,
                            den.eqNode(mkZero(den.getType())).negate(),
                            mkEquality(nm->mkNode(Kind::MULT, den, v), num));
      lems.push_back(mkSkolemLemma(lem, v));
      return v;
      break;
    }
    case Kind::DIVISION:
    {
      Node num = rewrite(node[0]);
      Node den = rewrite(node[1]);
      Node ret = nm->mkNode(Kind::DIVISION_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        checkNonLinearLogic(node);
        Node divByZeroNum = getArithSkolemApp(num, SkolemId::DIV_BY_ZERO);
        Node denEq0 = nm->mkNode(Kind::EQUAL, den, mkZero(den.getType()));
        ret = nm->mkNode(Kind::ITE, denEq0, divByZeroNum, ret);
      }
      return ret;
      break;
    }

    case Kind::INTS_DIVISION:
    {
      // partial function: integer div
      Node num = rewrite(node[0]);
      Node den = rewrite(node[1]);
      Node ret = nm->mkNode(Kind::INTS_DIVISION_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        checkNonLinearLogic(node);
        Node intDivByZeroNum =
            getArithSkolemApp(num, SkolemId::INT_DIV_BY_ZERO);
        Node denEq0 = nm->mkNode(Kind::EQUAL, den, nm->mkConstInt(Rational(0)));
        ret = nm->mkNode(Kind::ITE, denEq0, intDivByZeroNum, ret);
      }
      return ret;
      break;
    }

    case Kind::INTS_MODULUS:
    {
      // partial function: mod
      Node num = rewrite(node[0]);
      Node den = rewrite(node[1]);
      Node ret = nm->mkNode(Kind::INTS_MODULUS_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        checkNonLinearLogic(node);
        Node modZeroNum = getArithSkolemApp(num, SkolemId::MOD_BY_ZERO);
        Node denEq0 = nm->mkNode(Kind::EQUAL, den, nm->mkConstInt(Rational(0)));
        ret = nm->mkNode(Kind::ITE, denEq0, modZeroNum, ret);
      }
      return ret;
      break;
    }

    case Kind::ABS:
    {
      return nm->mkNode(
          Kind::ITE,
          nm->mkNode(Kind::LT,
                     node[0],
                     nm->mkConstRealOrInt(node[0].getType(), Rational(0))),
          nm->mkNode(Kind::NEG, node[0]),
          node[0]);
      break;
    }
    case Kind::SQRT:
    case Kind::ARCSINE:
    case Kind::ARCCOSINE:
    case Kind::ARCTANGENT:
    case Kind::ARCCOSECANT:
    case Kind::ARCSECANT:
    case Kind::ARCCOTANGENT:
    {
      if (partialOnly)
      {
        // not eliminating total operators
        return node;
      }
      checkNonLinearLogic(node);
      // We eliminate these functions using an uninterpreted function via
      // the skolem id TRANSCENDENTAL_PURIFY.
      // Make (lambda ((x Real)) (f x)) for this function, using the bound
      // variable manager to ensure this function is always the same.
      BoundVarManager* bvm = nm->getBoundVarManager();
      Node x = bvm->mkBoundVar<RealAlgebraicNumberVarAttribute>(
          node.getOperator(), "x", nm->realType());
      Node lam = nm->mkNode(
          Kind::LAMBDA, nm->mkNode(Kind::BOUND_VAR_LIST, x), nm->mkNode(k, x));
      Node fun = sm->mkSkolemFunction(SkolemId::TRANSCENDENTAL_PURIFY, lam);
      // Make (@TRANSCENDENTAL_PURIFY t), where t is node[0]
      Node var = nm->mkNode(Kind::APPLY_UF, fun, node[0]);
      Node lem;
      if (k == Kind::SQRT)
      {
        Node nonNeg = nm->mkNode(Kind::MULT, var, var).eqNode(node[0]);

        // (sqrt x) reduces to:
        // (=> (>= x 0.0) (= (* y y) x))
        // where y is (@TRANSCENDENTAL_PURIFY x).
        //
        // This makes sure that the reduction still behaves like a function,
        // otherwise the reduction of (x = 1) ^ (sqrt(x) != sqrt(1)) would be
        // satisfiable. On the original formula, this would require that we
        // simultaneously interpret sqrt(1) as 1 and -1, which is not a valid
        // model.
        lem = nm->mkNode(
            Kind::IMPLIES,
            nm->mkNode(Kind::GEQ, node[0], nm->mkConstReal(Rational(0))),
            nonNeg);
      }
      else
      {
        Node pi = mkPi();

        // range of the skolem
        Node rlem;
        if (k == Kind::ARCSINE || k == Kind::ARCTANGENT
            || k == Kind::ARCCOSECANT)
        {
          Node half = nm->mkConstReal(Rational(1) / Rational(2));
          Node pi2 = nm->mkNode(Kind::MULT, half, pi);
          Node npi2 =
              nm->mkNode(Kind::MULT, nm->mkConstReal(Rational(-1)), pi2);
          // -pi/2 < var <= pi/2
          rlem = nm->mkNode(Kind::AND,
                            nm->mkNode(Kind::LT, npi2, var),
                            nm->mkNode(Kind::LEQ, var, pi2));
        }
        else
        {
          // 0 <= var < pi
          rlem = nm->mkNode(
              Kind::AND,
              nm->mkNode(Kind::LEQ, nm->mkConstReal(Rational(0)), var),
              nm->mkNode(Kind::LT, var, pi));
        }
        Node cond;
        if (k == Kind::ARCSINE || k == Kind::ARCCOSINE || k == Kind::ARCSECANT
            || k == Kind::ARCCOSECANT)
        {
          // -1 <= x <= 1
          cond = nm->mkNode(
              Kind::AND,
              nm->mkNode(Kind::GEQ, node[0], nm->mkConstReal(Rational(-1))),
              nm->mkNode(Kind::LEQ, node[0], nm->mkConstReal(Rational(1))));
          if (k == Kind::ARCSECANT || k == Kind::ARCCOSECANT)
          {
            cond = cond.notNode();
          }
        }

        Kind rk;
        switch (k)
        {
          case Kind::ARCSINE: rk = Kind::SINE; break;
          case Kind::ARCCOSINE: rk = Kind::COSINE; break;
          case Kind::ARCTANGENT: rk = Kind::TANGENT; break;
          case Kind::ARCCOSECANT: rk = Kind::COSECANT; break;
          case Kind::ARCSECANT: rk = Kind::SECANT; break;
          case Kind::ARCCOTANGENT: rk = Kind::COTANGENT; break;
          default: Unreachable() << "Unexpected kind " << k;
        }
        Node invTerm = nm->mkNode(rk, var);
        lem = nm->mkNode(Kind::AND, rlem, mkEquality(invTerm, node[0]));
        if (!cond.isNull())
        {
          lem = nm->mkNode(Kind::IMPLIES, cond, lem);
        }
        Trace("arith-op-elim")
            << "Elimination lemma " << lem << " for " << node << std::endl;
      }
      Assert(!lem.isNull());
      lems.push_back(mkSkolemLemma(lem, var));
      return var;
    }
    case Kind::REAL_ALGEBRAIC_NUMBER:
    {
      BoundVarManager* bvm = nm->getBoundVarManager();
      Node v = bvm->mkBoundVar<RealAlgebraicNumberVarAttribute>(
          node, "i", nm->realType());
      Node w;
#ifdef CVC5_POLY_IMP
      w = PolyConverter::ran_to_node(
          node.getOperator().getConst<RealAlgebraicNumber>(), v);
#endif
      // it should not be possible to define real algebraic numbers unless poly
      // is enabled
      Assert(!w.isNull());
      return w;
    }

    default: break;
  }
  return node;
}

Node OperatorElim::getAxiomFor(Node n) { return Node::null(); }

Node OperatorElim::getArithSkolem(SkolemId id)
{
  std::map<SkolemId, Node>::iterator it = d_arithSkolem.find(id);
  if (it == d_arithSkolem.end())
  {
    NodeManager* nm = nodeManager();
    Node skolem;
    SkolemManager* sm = nm->getSkolemManager();
    // introduce the skolem function
    skolem = sm->mkSkolemFunction(id);
    // cache it
    d_arithSkolem[id] = skolem;
    return skolem;
  }
  return it->second;
}

Node OperatorElim::getArithSkolemApp(Node n, SkolemId id)
{
  Node skolem = getArithSkolem(id);
  NodeManager* nm = nodeManager();
  if (usePartialFunction(id))
  {
    Assert(skolem.getType().isFunction()
           && skolem.getType().getNumChildren() == 2);
    TypeNode argType = skolem.getType()[0];
    if (!argType.isInteger() && n.getType().isInteger())
    {
      n = nm->mkNode(Kind::TO_REAL, n);
    }
    skolem = nm->mkNode(Kind::APPLY_UF, skolem, n);
  }
  else
  {
    // We return the purify skolem for (<id> 0). Note this is necessary to
    // ensure we can give a consistent type for the skolem function <id>,
    // independent of the option arithNoPartialFun.
    SkolemManager* sm = nm->getSkolemManager();
    Node kapp = nm->mkNode(
        Kind::APPLY_UF, skolem, nm->mkConstRealOrInt(n.getType(), Rational(0)));
    skolem = sm->mkPurifySkolem(kapp);
  }
  return skolem;
}

bool OperatorElim::usePartialFunction(SkolemId id) const
{
  // always use partial function for sqrt
  return !options().arith.arithNoPartialFun
         || id == SkolemId::TRANSCENDENTAL_PURIFY;
}

SkolemLemma OperatorElim::mkSkolemLemma(Node lem, Node k)
{
  TrustNode tlem;
  if (d_env.isTheoryProofProducing())
  {
    Node tid = mkTrustId(TrustId::THEORY_PREPROCESS_LEMMA);
    tlem = mkTrustNode(lem, ProofRule::TRUST, {}, {tid, lem});
  }
  else
  {
    tlem = TrustNode::mkTrustLemma(lem, nullptr);
  }
  return SkolemLemma(tlem, k);
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
