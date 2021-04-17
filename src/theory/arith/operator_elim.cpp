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
 * Implementation of operator elimination for arithmetic.
 */

#include "theory/arith/operator_elim.h"

#include <sstream>

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/term_conversion_proof_generator.h"
#include "options/arith_options.h"
#include "smt/logic_exception.h"
#include "theory/arith/arith_utilities.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arith {

/**
 * Attribute used for constructing unique bound variables that are binders
 * for witness terms below. In other words, this attribute maps nodes to
 * the bound variable of a witness term for eliminating that node.
 *
 * Notice we use the same attribute for most bound variables below, since using
 * a node itself is a sufficient cache key for constructing a bound variable.
 * The exception is to_int / is_int, which share a skolem based on their
 * argument.
 */
struct ArithWitnessVarAttributeId
{
};
using ArithWitnessVarAttribute = expr::Attribute<ArithWitnessVarAttributeId, Node>;
/**
 * Similar to above, shared for to_int and is_int. This is used for introducing
 * an integer bound variable used to construct the witness term for t in the
 * contexts (to_int t) and (is_int t).
 */
struct ToIntWitnessVarAttributeId
{
};
using ToIntWitnessVarAttribute
 = expr::Attribute<ToIntWitnessVarAttributeId, Node>;

OperatorElim::OperatorElim(ProofNodeManager* pnm, const LogicInfo& info)
    : EagerProofGenerator(pnm), d_info(info)
{
}

void OperatorElim::checkNonLinearLogic(Node term)
{
  if (d_info.isLinear())
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
  BoundVarManager* bvm = nm->getBoundVarManager();
  Kind k = node.getKind();
  switch (k)
  {
    case TANGENT:
    case COSECANT:
    case SECANT:
    case COTANGENT:
    {
      // these are eliminated by rewriting
      return Rewriter::rewrite(node);
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
      Node v =
          bvm->mkBoundVar<ToIntWitnessVarAttribute>(node[0], nm->integerType());
      Node one = mkRationalNode(1);
      Node zero = mkRationalNode(0);
      Node diff = nm->mkNode(MINUS, node[0], v);
      Node lem = mkInRange(diff, zero, one);
      Node toIntSkolem =
          mkWitnessTerm(v,
                        lem,
                        "toInt",
                        "a conversion of a Real term to its Integer part",
                        lems);
      if (k == IS_INTEGER)
      {
        return nm->mkNode(EQUAL, node[0], toIntSkolem);
      }
      Assert(k == TO_INTEGER);
      return toIntSkolem;
    }

    case INTS_DIVISION_TOTAL:
    case INTS_MODULUS_TOTAL:
    {
      if (partialOnly)
      {
        // not eliminating total operators
        return node;
      }
      Node den = Rewriter::rewrite(node[1]);
      Node num = Rewriter::rewrite(node[0]);
      Node rw = nm->mkNode(k, num, den);
      Node v = bvm->mkBoundVar<ArithWitnessVarAttribute>(rw, nm->integerType());
      Node lem;
      Node leqNum = nm->mkNode(LEQ, nm->mkNode(MULT, den, v), num);
      if (den.isConst())
      {
        const Rational& rat = den.getConst<Rational>();
        if (num.isConst() || rat == 0)
        {
          // just rewrite
          return Rewriter::rewrite(node);
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
                             nm->mkNode(PLUS, v, nm->mkConst(Rational(1))))));
        }
        else
        {
          lem = nm->mkNode(
              AND,
              leqNum,
              nm->mkNode(
                  LT,
                  num,
                  nm->mkNode(MULT,
                             den,
                             nm->mkNode(PLUS, v, nm->mkConst(Rational(-1))))));
        }
      }
      else
      {
        checkNonLinearLogic(node);
        lem = nm->mkNode(
            AND,
            nm->mkNode(
                IMPLIES,
                nm->mkNode(GT, den, nm->mkConst(Rational(0))),
                nm->mkNode(
                    AND,
                    leqNum,
                    nm->mkNode(
                        LT,
                        num,
                        nm->mkNode(
                            MULT,
                            den,
                            nm->mkNode(PLUS, v, nm->mkConst(Rational(1))))))),
            nm->mkNode(
                IMPLIES,
                nm->mkNode(LT, den, nm->mkConst(Rational(0))),
                nm->mkNode(
                    AND,
                    leqNum,
                    nm->mkNode(
                        LT,
                        num,
                        nm->mkNode(
                            MULT,
                            den,
                            nm->mkNode(PLUS, v, nm->mkConst(Rational(-1))))))));
      }
      Node intVar = mkWitnessTerm(
          v, lem, "linearIntDiv", "the result of an intdiv-by-k term", lems);
      if (k == INTS_MODULUS_TOTAL)
      {
        Node nn = nm->mkNode(MINUS, num, nm->mkNode(MULT, den, intVar));
        return nn;
      }
      else
      {
        return intVar;
      }
      break;
    }
    case DIVISION_TOTAL:
    {
      if (partialOnly)
      {
        // not eliminating total operators
        return node;
      }
      Node num = Rewriter::rewrite(node[0]);
      Node den = Rewriter::rewrite(node[1]);
      if (den.isConst())
      {
        // No need to eliminate here, can eliminate via rewriting later.
        // Moreover, rewriting may change the type of this node from real to
        // int, which impacts certain issues with subtyping.
        return node;
      }
      checkNonLinearLogic(node);
      Node rw = nm->mkNode(k, num, den);
      Node v = bvm->mkBoundVar<ArithWitnessVarAttribute>(rw, nm->realType());
      Node lem = nm->mkNode(IMPLIES,
                            den.eqNode(nm->mkConst(Rational(0))).negate(),
                            nm->mkNode(MULT, den, v).eqNode(num));
      return mkWitnessTerm(
          v, lem, "nonlinearDiv", "the result of a non-linear div term", lems);
      break;
    }
    case DIVISION:
    {
      Node num = Rewriter::rewrite(node[0]);
      Node den = Rewriter::rewrite(node[1]);
      Node ret = nm->mkNode(DIVISION_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        checkNonLinearLogic(node);
        Node divByZeroNum = getArithSkolemApp(num, SkolemFunId::DIV_BY_ZERO);
        Node denEq0 = nm->mkNode(EQUAL, den, nm->mkConst(Rational(0)));
        ret = nm->mkNode(ITE, denEq0, divByZeroNum, ret);
      }
      return ret;
      break;
    }

    case INTS_DIVISION:
    {
      // partial function: integer div
      Node num = Rewriter::rewrite(node[0]);
      Node den = Rewriter::rewrite(node[1]);
      Node ret = nm->mkNode(INTS_DIVISION_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        checkNonLinearLogic(node);
        Node intDivByZeroNum =
            getArithSkolemApp(num, SkolemFunId::INT_DIV_BY_ZERO);
        Node denEq0 = nm->mkNode(EQUAL, den, nm->mkConst(Rational(0)));
        ret = nm->mkNode(ITE, denEq0, intDivByZeroNum, ret);
      }
      return ret;
      break;
    }

    case INTS_MODULUS:
    {
      // partial function: mod
      Node num = Rewriter::rewrite(node[0]);
      Node den = Rewriter::rewrite(node[1]);
      Node ret = nm->mkNode(INTS_MODULUS_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        checkNonLinearLogic(node);
        Node modZeroNum = getArithSkolemApp(num, SkolemFunId::MOD_BY_ZERO);
        Node denEq0 = nm->mkNode(EQUAL, den, nm->mkConst(Rational(0)));
        ret = nm->mkNode(ITE, denEq0, modZeroNum, ret);
      }
      return ret;
      break;
    }

    case ABS:
    {
      return nm->mkNode(ITE,
                        nm->mkNode(LT, node[0], nm->mkConst(Rational(0))),
                        nm->mkNode(UMINUS, node[0]),
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
      Node var =
          bvm->mkBoundVar<ArithWitnessVarAttribute>(node, nm->realType());
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
                         nm->mkNode(GEQ, node[0], nm->mkConst(Rational(0))),
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
          Node half = nm->mkConst(Rational(1) / Rational(2));
          Node pi2 = nm->mkNode(MULT, half, pi);
          Node npi2 = nm->mkNode(MULT, nm->mkConst(Rational(-1)), pi2);
          // -pi/2 < var <= pi/2
          rlem = nm->mkNode(
              AND, nm->mkNode(LT, npi2, var), nm->mkNode(LEQ, var, pi2));
        }
        else
        {
          // 0 <= var < pi
          rlem = nm->mkNode(AND,
                            nm->mkNode(LEQ, nm->mkConst(Rational(0)), var),
                            nm->mkNode(LT, var, pi));
        }

        Kind rk =
            k == ARCSINE
                ? SINE
                : (k == ARCCOSINE
                       ? COSINE
                       : (k == ARCTANGENT
                              ? TANGENT
                              : (k == ARCCOSECANT
                                     ? COSECANT
                                     : (k == ARCSECANT ? SECANT : COTANGENT))));
        Node invTerm = nm->mkNode(rk, var);
        lem = nm->mkNode(AND, rlem, invTerm.eqNode(node[0]));
      }
      Assert(!lem.isNull());
      return mkWitnessTerm(
          var,
          lem,
          "tfk",
          "Skolem to eliminate a non-standard transcendental function",
          lems);
      break;
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
    if (options::arithNoPartialFun())
    {
      // partial function: division, where we treat the skolem function as
      // a constant
      skolem = sm->mkSkolemFunction(id, tn);
    }
    else
    {
      // partial function: division
      skolem = sm->mkSkolemFunction(id, nm->mkFunctionType(tn, tn));
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
  if (!options::arithNoPartialFun())
  {
    skolem = NodeManager::currentNM()->mkNode(APPLY_UF, skolem, n);
  }
  return skolem;
}

Node OperatorElim::mkWitnessTerm(Node v,
                                 Node pred,
                                 const std::string& prefix,
                                 const std::string& comment,
                                 std::vector<SkolemLemma>& lems)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  // we mark that we should send a lemma
  Node k =
      sm->mkSkolem(v, pred, prefix, comment, NodeManager::SKOLEM_DEFAULT, this);
  if (d_pnm != nullptr)
  {
    Node lem = SkolemLemma::getSkolemLemmaFor(k);
    TrustNode tlem =
        mkTrustNode(lem, PfRule::THEORY_PREPROCESS_LEMMA, {}, {lem});
    lems.push_back(SkolemLemma(tlem, k));
  }
  else
  {
    lems.push_back(SkolemLemma(k, nullptr));
  }
  return k;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
