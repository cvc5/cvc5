/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of operator elimination for arithmetic.
 */

#include "theory/arith/operator_elim.h"

#include <sstream>

#include "expr/bound_var_manager.h"
#include "options/arith_options.h"
#include "proof/proof_node_manager.h"
#include "proof/trust_id.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/nl/poly_conversion.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "proof/proof.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {

OperatorElim::OperatorElim(Env& env) : EnvObj(env), d_lemmaMap(userContext()) {}

TrustNode OperatorElim::eliminate(Node n,
                                  std::vector<SkolemLemma>& lems,
                                  bool partialOnly)
{
  Assert(rewrite(n) == n);
  NodeManager* nm = nodeManager();
  std::vector<std::pair<Node, Node>> klems;
  bool wasNonLinear = false;
  Node nn = eliminateOperators(nm, n, klems, partialOnly, wasNonLinear);
  if (nn == n)
  {
    return TrustNode::null();
  }
  // logic exception if non-linear
  if (wasNonLinear)
  {
    if (logicInfo().isLinear())
    {
      Trace("arith-logic") << "ERROR: Non-linear term in linear logic: " << n
                           << std::endl;
      std::stringstream serr;
      serr << "A non-linear fact was asserted to arithmetic in a linear logic."
           << std::endl;
      serr << "The fact in question: " << n << std::endl;
      throw LogicException(serr.str());
    }
  }
  // if transcendental, we don't eliminate if not expert
  if (isTranscendentalKind(n.getKind()))
  {
    if (!options().arith.arithExp)
    {
      return TrustNode::null();
    }
  }
  // should only be a single lemma, if there is one
  Assert(klems.size() <= 1);
  for (std::pair<Node, Node>& p : klems)
  {
    // each skolem lemma can be justified by this class
    lems.emplace_back(mkSkolemLemma(p.first, p.second, n));
  }
  // we can provide a proof for the rewrite as well
  return TrustNode::mkTrustRewrite(n, nn, this);
}

Node OperatorElim::eliminateOperators(NodeManager* nm,
                                      Node node,
                                      std::vector<std::pair<Node, Node>>& lems,
                                      bool partialOnly,
                                      bool& wasNonLinear)
{
  Trace("arith-op-elim") << "node: " << node << std::endl;
  SkolemManager* sm = nm->getSkolemManager();
  Kind k = node.getKind();
  switch (k)
  {
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
      Node vr = nm->mkNode(Kind::TO_REAL, v);
      Node one = nm->mkConstReal(Rational(1));
      Node zero = nm->mkConstReal(Rational(0));
      Node diff = nm->mkNode(Kind::SUB, node[0], vr);
      Node lem = mkInRange(diff, zero, one);
      lems.emplace_back(lem, v);
      if (k == Kind::IS_INTEGER)
      {
        return nm->mkNode(Kind::EQUAL, node[0], vr);
      }
      Assert(k == Kind::TO_INTEGER);
      return v;
    }
    case Kind::INTS_LOG2:
    {
      if (partialOnly)
      {
        // not eliminating total operators
        return node;
      }
      // for a fresh skolem v, the elimination is:
      // (int.log2 x) --> v, with lemmas: 
      // (=> (> x 0) (and (<= (int.pow2 v) x) (< x (* 2 (int.pow2 v)))))
      // (=> (<= x 0) (= v 0))
      Node zero = nm->mkConstInt(Integer(0));
      Node one = nm->mkConstInt(Integer(1));
      Node x = node[0];
      Node v = sm->mkPurifySkolem(node);
      Node sv = nm->mkNode(Kind::ADD, v, one);
      Node ptv = nm->mkNode(Kind::POW2, v);
      Node ptv1 = nm->mkNode(Kind::POW2, sv);
      Node pos_assumption = nm->mkNode(Kind::LT, zero, x);
      Node pos_prop1 = nm->mkNode(Kind::LEQ, ptv, x);
      Node pos_prop2 = nm->mkNode(Kind::LT, x, ptv1);
      Node pos_prop = nm->mkNode(Kind::AND, pos_prop1, pos_prop2);
      Node pos_lem = nm->mkNode(Kind::IMPLIES, pos_assumption, pos_prop);
      
      Node neg_assumption = nm->mkNode(Kind::NOT, pos_assumption);
      Node neg_prop = nm->mkNode(Kind::EQUAL, v, zero);
      Node neg_lem = nm->mkNode(Kind::IMPLIES, neg_assumption, neg_prop);
      Node lem = nm->mkNode(Kind::AND, pos_lem, neg_lem);
      lems.emplace_back(lem, v);

      Trace("arith-op-elim") << "INTS_LOG2: node" << node << std::endl;
      Trace("arith-op-elim") << "INTS_LOG2: x" << x << std::endl;
      Trace("arith-op-elim") << "INTS_LOG2: v" << v << std::endl;
      Trace("arith-op-elim") << "INTS_LOG2: lem" << lem << std::endl;
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
      // we use the purification skolem for div
      Node den = node[1];
      Node num = node[0];
      Node pterm = nm->mkNode(Kind::INTS_DIVISION_TOTAL, node[0], node[1]);
      Node v = sm->mkPurifySkolem(pterm);
      // make the corresponding lemma
      Node lem;
      Node leqNum = nm->mkNode(Kind::LEQ, nm->mkNode(Kind::MULT, den, v), num);
      if (den.isConst())
      {
        const Rational& rat = den.getConst<Rational>();
        Assert(!num.isConst() && rat.sgn() != 0);
        lem = nm->mkNode(
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
                               nm->mkConstInt(Rational(rat > 0 ? 1 : -1))))));
      }
      else
      {
        wasNonLinear = true;
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
      lems.emplace_back(lem, v);
      Trace("arith-op-elim") << "lem " << lem << std::endl;
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
      Node num = node[0];
      Node den = node[1];
      if (den.isConst())
      {
        // No need to eliminate here, can eliminate via rewriting later.
        // Moreover, rewriting may change the type of this node from real to
        // int, which impacts certain issues with subtyping.
        return node;
      }
      wasNonLinear = true;
      Node rw = nm->mkNode(k, num, den);
      Node v = sm->mkPurifySkolem(rw);
      if (num.getType().isInteger())
      {
        num = nm->mkNode(Kind::TO_REAL, num);
      }
      Node lem = nm->mkNode(
          Kind::IMPLIES,
          den.eqNode(mkZero(den.getType())).negate(),
          nm->mkNode(Kind::EQUAL, nm->mkNode(Kind::MULT, den, v), num));
      lems.emplace_back(lem, v);
      return v;
      break;
    }
    case Kind::DIVISION:
    {
      Node num = node[0];
      Node den = node[1];
      Node ret = nm->mkNode(Kind::DIVISION_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        wasNonLinear = true;
        Node divByZeroNum = getArithSkolemApp(nm, num, SkolemId::DIV_BY_ZERO);
        Node denEq0 = nm->mkNode(Kind::EQUAL, den, mkZero(den.getType()));
        ret = nm->mkNode(Kind::ITE, denEq0, divByZeroNum, ret);
      }
      return ret;
      break;
    }

    case Kind::INTS_DIVISION:
    {
      // partial function: integer div
      Node num = node[0];
      Node den = node[1];
      Node ret = nm->mkNode(Kind::INTS_DIVISION_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        wasNonLinear = true;
        Node intDivByZeroNum =
            getArithSkolemApp(nm, num, SkolemId::INT_DIV_BY_ZERO);
        Node denEq0 = nm->mkNode(Kind::EQUAL, den, nm->mkConstInt(Rational(0)));
        ret = nm->mkNode(Kind::ITE, denEq0, intDivByZeroNum, ret);
      }
      return ret;
      break;
    }

    case Kind::INTS_MODULUS:
    {
      // partial function: mod
      Node num = node[0];
      Node den = node[1];
      Node ret = nm->mkNode(Kind::INTS_MODULUS_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        wasNonLinear = true;
        Node modZeroNum = getArithSkolemApp(nm, num, SkolemId::MOD_BY_ZERO);
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
      wasNonLinear = true;
      // We eliminate these functions using an uninterpreted function via
      // the skolem id TRANSCENDENTAL_PURIFY.
      // Make (lambda ((x Real)) (f x)) for this function, using the bound
      // variable manager to ensure this function is always the same.
      BoundVarManager* bvm = nm->getBoundVarManager();
      Node x = bvm->mkBoundVar(
          BoundVarId::ARITH_TR_PURIFY, node.getOperator(), "x", nm->realType());
      Node lam = nm->mkNode(
          Kind::LAMBDA, nm->mkNode(Kind::BOUND_VAR_LIST, x), nm->mkNode(k, x));
      Node fun = sm->mkSkolemFunction(SkolemId::TRANSCENDENTAL_PURIFY, lam);
      // Make (@TRANSCENDENTAL_PURIFY t), where t is node[0]
      Node var = nm->mkNode(Kind::APPLY_UF, fun, node[0]);
      Node lem;
      if (k == Kind::SQRT)
      {
        Node zero = nm->mkConstReal(Rational(0));
        Node eq = nm->mkNode(Kind::MULT, var, var).eqNode(node[0]);
        Node resNonNeg = nm->mkNode(Kind::GEQ, var, zero);

        // (sqrt x) reduces to:
        // (=> (>= x 0.0) (and (>= y 0.0) (= (* y y) x))
        // where y is (@TRANSCENDENTAL_PURIFY x).
        //
        // This makes sure that the reduction still behaves like a function,
        // otherwise the reduction of (x = -1) ^ (sqrt(x) != sqrt(-1)) would be
        // satisfiable.
        lem = nm->mkNode(Kind::IMPLIES,
                         nm->mkNode(Kind::GEQ, node[0], zero),
                         nm->mkNode(Kind::AND, resNonNeg, eq));
      }
      else
      {
        Node pi = mkPi(nm);

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
      // the skolem lemma is for the function
      lems.emplace_back(lem, fun);
      return var;
    }
    case Kind::REAL_ALGEBRAIC_NUMBER:
    {
      BoundVarManager* bvm = nm->getBoundVarManager();
      Node v = bvm->mkBoundVar(
          BoundVarId::REAL_ALGEBRAIC_NUMBER_WITNESS, node, "i", nm->realType());
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
    // these are handled by rewriting
    default: break;
  }
  return node;
}

Node OperatorElim::getAxiomFor(NodeManager* nm, const Node& n)
{
  std::vector<std::pair<Node, Node>> klems;
  bool wasNonLinear = false;
  Node nn = eliminateOperators(nm, n, klems, false, wasNonLinear);
  if (nn==n)
  {
    return Node::null();
  }
  Node eqLem = n.eqNode(nn);
  std::vector<Node> lemmas;
  for (const std::pair<Node, Node>& kl : klems)
  {
    lemmas.emplace_back(kl.first);
  }
  if (!lemmas.empty())
  {
    Node axiom = nm->mkAnd(lemmas);
    return nm->mkNode(Kind::AND, eqLem, axiom);
  }
  return eqLem;
}

Node OperatorElim::getArithSkolemApp(NodeManager* nm, Node n, SkolemId id)
{
  SkolemManager* sm = nm->getSkolemManager();
  Node skolem = sm->mkSkolemFunction(id);
  Assert(skolem.getType().isFunction()
         && skolem.getType().getNumChildren() == 2);
  TypeNode argType = skolem.getType()[0];
  if (!argType.isInteger() && n.getType().isInteger())
  {
    n = nm->mkNode(Kind::TO_REAL, n);
  }
  skolem = nm->mkNode(Kind::APPLY_UF, skolem, n);
  return skolem;
}

SkolemLemma OperatorElim::mkSkolemLemma(const Node& lem,
                                        const Node& k,
                                        const Node& n)
{
  TrustNode tlem;
  if (d_env.isTheoryProofProducing())
  {
    tlem = TrustNode::mkTrustLemma(lem, this);
    d_lemmaMap[lem] = n;
  }
  else
  {
    tlem = TrustNode::mkTrustLemma(lem, nullptr);
  }
  return SkolemLemma(tlem, k);
}

std::shared_ptr<ProofNode> OperatorElim::getProofFor(Node f)
{
  // This class provides proofs for two things:
  // (1) rewrites n --> nn during preprocessing,
  // (2) the axioms A added when rewriting n ---> nn.
  // The proof rule ARITH_REDUCTION proves things of the form:
  //    (and (= n nn) A)
  // where A may be omitted. We first determine which case we are in (whether
  // being asked for a proof of a preprocessing rewrite or an axiom) and store
  // the target term (n above) into tgt.
  context::CDHashMap<Node, Node>::iterator it = d_lemmaMap.find(f);
  Node tgt;
  if (it == d_lemmaMap.end())
  {
    if (f.getKind()!=Kind::EQUAL)
    {
      Assert(false) << "arith::OperatorElim could not prove " << f;
      return nullptr;
    }
    // target is the left hand side.
    tgt = f[0];
  }
  else
  {
    // target was stored in d_lemmaMap for an axiom.
    tgt = it->second;
  }
  CDProof cdp(d_env);
  Node res = getAxiomFor(nodeManager(), tgt);
  cdp.addStep(res, ProofRule::ARITH_REDUCTION, {}, {tgt});
  bool success = false;
  // If the axiom was an AND, then the fact in question should be one of the
  // conjuncts, in which case we do an AND_ELIM step.
  if (res.getKind()==Kind::AND)
  {
    Assert (res.getNumChildren()==2);
    for (size_t i=0; i<2; i++)
    {
      if (res[i]==f)
      {
        Node ni = nodeManager()->mkConstInt(i);
        cdp.addStep(f, ProofRule::AND_ELIM, {res}, {ni});
        success = true;
        break;
      }
    }
  }
  else
  {
    success = (res==f);
  }
  Assert(success) << "arith::OperatorElim could not prove " << f;
  if (!success)
  {
    return nullptr;
  }
  return cdp.getProofFor(f);
}

std::string OperatorElim::identify() const { return "arith::OperatorElim"; }

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
