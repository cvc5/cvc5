/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Kind k = node.getKind();
  switch (k)
  {
    case TANGENT:
    case COSECANT:
    case SECANT:
    case COTANGENT:
    {
      // these are eliminated by rewriting
      return rewrite(node);
      break;
    }
    case TO_INTEGER:
    case IS_INTEGER:
    {
      if (partialOnly)
      {
        // not eliminating total operators
        return node;
      }
      // node[0] - 1 < toIntSkolem <= node[0]
      // -1 < toIntSkolem - node[0] <= 0
      // 0 <= node[0] - toIntSkolem < 1
      Node pterm = nm->mkNode(TO_INTEGER, node[0]);
      Node v = sm->mkPurifySkolem(pterm);
      Node one = nm->mkConstReal(Rational(1));
      Node zero = nm->mkConstReal(Rational(0));
      Node diff = nm->mkNode(SUB, node[0], v);
      Node lem = mkInRange(diff, zero, one);
      lems.push_back(mkSkolemLemma(lem, v));
      if (k == IS_INTEGER)
      {
        return mkEquality(node[0], v);
      }
      Assert(k == TO_INTEGER);
      return v;
    }

    case INTS_DIVISION_TOTAL:
    case INTS_MODULUS_TOTAL:
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
      Node pterm = nm->mkNode(INTS_DIVISION_TOTAL, node[0], node[1]);
      Node v = sm->mkPurifySkolem(pterm);
      // make the corresponding lemma
      Node lem;
      Node leqNum = nm->mkNode(LEQ, nm->mkNode(MULT, den, v), num);
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
              AND,
              leqNum,
              nm->mkNode(
                  LT,
                  num,
                  nm->mkNode(MULT,
                             den,
                             nm->mkNode(ADD, v, nm->mkConstInt(Rational(1))))));
        }
        else
        {
          lem = nm->mkNode(
              AND,
              leqNum,
              nm->mkNode(
                  LT,
                  num,
                  nm->mkNode(
                      MULT,
                      den,
                      nm->mkNode(ADD, v, nm->mkConstInt(Rational(-1))))));
        }
      }
      else
      {
        checkNonLinearLogic(node);
        lem = nm->mkNode(
            AND,
            nm->mkNode(
                IMPLIES,
                nm->mkNode(GT, den, nm->mkConstInt(Rational(0))),
                nm->mkNode(
                    AND,
                    leqNum,
                    nm->mkNode(
                        LT,
                        num,
                        nm->mkNode(
                            MULT,
                            den,
                            nm->mkNode(ADD, v, nm->mkConstInt(Rational(1))))))),
            nm->mkNode(
                IMPLIES,
                nm->mkNode(LT, den, nm->mkConstInt(Rational(0))),
                nm->mkNode(
                    AND,
                    leqNum,
                    nm->mkNode(
                        LT,
                        num,
                        nm->mkNode(
                            MULT,
                            den,
                            nm->mkNode(
                                ADD, v, nm->mkConstInt(Rational(-1))))))));
      }
      // add the skolem lemma to lems
      lems.push_back(mkSkolemLemma(lem, v));
      if (k == INTS_MODULUS_TOTAL)
      {
        Node nn = nm->mkNode(SUB, num, nm->mkNode(MULT, den, v));
        return nn;
      }
      return v;
    }
    case DIVISION_TOTAL:
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
      Node lem = nm->mkNode(IMPLIES,
                            den.eqNode(mkZero(den.getType())).negate(),
                            mkEquality(nm->mkNode(MULT, den, v), num));
      lems.push_back(mkSkolemLemma(lem, v));
      return v;
      break;
    }
    case DIVISION:
    {
      Node num = rewrite(node[0]);
      Node den = rewrite(node[1]);
      Node ret = nm->mkNode(DIVISION_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        checkNonLinearLogic(node);
        Node divByZeroNum = getArithSkolemApp(num, SkolemFunId::DIV_BY_ZERO);
        Node denEq0 = nm->mkNode(EQUAL, den, mkZero(den.getType()));
        ret = nm->mkNode(ITE, denEq0, divByZeroNum, ret);
      }
      return ret;
      break;
    }

    case INTS_DIVISION:
    {
      // partial function: integer div
      Node num = rewrite(node[0]);
      Node den = rewrite(node[1]);
      Node ret = nm->mkNode(INTS_DIVISION_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        checkNonLinearLogic(node);
        Node intDivByZeroNum =
            getArithSkolemApp(num, SkolemFunId::INT_DIV_BY_ZERO);
        Node denEq0 = nm->mkNode(EQUAL, den, nm->mkConstInt(Rational(0)));
        ret = nm->mkNode(ITE, denEq0, intDivByZeroNum, ret);
      }
      return ret;
      break;
    }

    case INTS_MODULUS:
    {
      // partial function: mod
      Node num = rewrite(node[0]);
      Node den = rewrite(node[1]);
      Node ret = nm->mkNode(INTS_MODULUS_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        checkNonLinearLogic(node);
        Node modZeroNum = getArithSkolemApp(num, SkolemFunId::MOD_BY_ZERO);
        Node denEq0 = nm->mkNode(EQUAL, den, nm->mkConstInt(Rational(0)));
        ret = nm->mkNode(ITE, denEq0, modZeroNum, ret);
      }
      return ret;
      break;
    }

    case ABS:
    {
      return nm->mkNode(
          ITE,
          nm->mkNode(LT,
                     node[0],
                     nm->mkConstRealOrInt(node[0].getType(), Rational(0))),
          nm->mkNode(NEG, node[0]),
          node[0]);
      break;
    }
    case SQRT:
    case ARCSINE:
    case ARCCOSINE:
    case ARCTANGENT:
    case ARCCOSECANT:
    case ARCSECANT:
    case ARCCOTANGENT:
    {
      if (partialOnly)
      {
        // not eliminating total operators
        return node;
      }
      checkNonLinearLogic(node);
      // eliminate inverse functions here
      Node var = sm->mkPurifySkolem(node);
      Node lem;
      if (k == SQRT)
      {
        Node skolemApp = getArithSkolemApp(node[0], SkolemFunId::SQRT);
        Node uf = skolemApp.eqNode(var);
        Node nonNeg =
            nm->mkNode(AND, nm->mkNode(MULT, var, var).eqNode(node[0]), uf);

        // sqrt(x) reduces to:
        // witness y. ite(x >= 0.0, y * y = x ^ y = Uf(x), y = Uf(x))
        //
        // Uf(x) makes sure that the reduction still behaves like a function,
        // otherwise the reduction of (x = 1) ^ (sqrt(x) != sqrt(1)) would be
        // satisfiable. On the original formula, this would require that we
        // simultaneously interpret sqrt(1) as 1 and -1, which is not a valid
        // model.
        lem = nm->mkNode(ITE,
                         nm->mkNode(GEQ, node[0], nm->mkConstReal(Rational(0))),
                         nonNeg,
                         uf);
      }
      else
      {
        Node pi = mkPi();

        // range of the skolem
        Node rlem;
        if (k == ARCSINE || k == ARCTANGENT || k == ARCCOSECANT)
        {
          Node half = nm->mkConstReal(Rational(1) / Rational(2));
          Node pi2 = nm->mkNode(MULT, half, pi);
          Node npi2 = nm->mkNode(MULT, nm->mkConstReal(Rational(-1)), pi2);
          // -pi/2 < var <= pi/2
          rlem = nm->mkNode(
              AND, nm->mkNode(LT, npi2, var), nm->mkNode(LEQ, var, pi2));
        }
        else
        {
          // 0 <= var < pi
          rlem = nm->mkNode(AND,
                            nm->mkNode(LEQ, nm->mkConstReal(Rational(0)), var),
                            nm->mkNode(LT, var, pi));
        }
        Node cond;
        if (k == ARCSINE || k == ARCCOSINE || k == ARCSECANT
            || k == ARCCOSECANT)
        {
          // -1 <= x <= 1
          cond = nm->mkNode(
              AND,
              nm->mkNode(GEQ, node[0], nm->mkConstReal(Rational(-1))),
              nm->mkNode(LEQ, node[0], nm->mkConstReal(Rational(1))));
          if (k == ARCSECANT || k == ARCCOSECANT)
          {
            cond = cond.notNode();
          }
        }

        Kind rk;
        switch (k)
        {
          case ARCSINE: rk = SINE; break;
          case ARCCOSINE: rk = COSINE; break;
          case ARCTANGENT: rk = TANGENT; break;
          case ARCCOSECANT: rk = COSECANT; break;
          case ARCSECANT: rk = SECANT; break;
          case ARCCOTANGENT: rk = COTANGENT; break;
          default: Unreachable() << "Unexpected kind " << k;
        }
        Node invTerm = nm->mkNode(rk, var);
        lem = nm->mkNode(AND, rlem, mkEquality(invTerm, node[0]));
        if (!cond.isNull())
        {
          lem = nm->mkNode(IMPLIES, cond, lem);
        }
      }
      Assert(!lem.isNull());
      lems.push_back(mkSkolemLemma(lem, var));
      return var;
    }
    case REAL_ALGEBRAIC_NUMBER:
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

Node OperatorElim::getArithSkolem(SkolemFunId id)
{
  std::map<SkolemFunId, Node>::iterator it = d_arithSkolem.find(id);
  if (it == d_arithSkolem.end())
  {
    NodeManager* nm = NodeManager::currentNM();
    TypeNode tn;
    if (id == SkolemFunId::DIV_BY_ZERO || id == SkolemFunId::SQRT)
    {
      tn = nm->realType();
    }
    else
    {
      tn = nm->integerType();
    }
    Node skolem;
    SkolemManager* sm = nm->getSkolemManager();
    if (usePartialFunction(id))
    {
      // partial function: division
      skolem = sm->mkSkolemFunction(id, nm->mkFunctionType(tn, tn));
    }
    else
    {
      // partial function: division, where we treat the skolem function as
      // a constant
      skolem = sm->mkSkolemFunction(id, tn);
    }
    // cache it
    d_arithSkolem[id] = skolem;
    return skolem;
  }
  return it->second;
}

Node OperatorElim::getArithSkolemApp(Node n, SkolemFunId id)
{
  Node skolem = getArithSkolem(id);
  if (usePartialFunction(id))
  {
    NodeManager* nm = NodeManager::currentNM();
    Assert(skolem.getType().isFunction()
           && skolem.getType().getNumChildren() == 2);
    TypeNode argType = skolem.getType()[0];
    if (!argType.isInteger() && n.getType().isInteger())
    {
      n = nm->mkNode(TO_REAL, n);
    }
    skolem = nm->mkNode(APPLY_UF, skolem, n);
  }
  return skolem;
}

bool OperatorElim::usePartialFunction(SkolemFunId id) const
{
  // always use partial function for sqrt
  return !options().arith.arithNoPartialFun || id == SkolemFunId::SQRT;
}

SkolemLemma OperatorElim::mkSkolemLemma(Node lem, Node k)
{
  TrustNode tlem;
  if (d_env.isTheoryProofProducing())
  {
    tlem = mkTrustNode(lem, PfRule::THEORY_PREPROCESS_LEMMA, {}, {lem});
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
