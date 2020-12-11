/*********************                                                        */
/*! \file proof_checker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof checker for transcendentals
 **/

#include "theory/arith/nl/transcendental/proof_checker.h"

#include "expr/sequence.h"
#include "theory/arith/arith_utilities.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

namespace {

/**
 * Evaluates the first d terms of the Maclaurin series for the exponential
 * function at t. This is a lower bound on the exponential function.
 */
inline Node evalMaclaurinExp(std::uint64_t d, TNode t)
{
  auto* nm = NodeManager::currentNM();
  Node res = nm->mkConst<Rational>(1);
  Node num = nm->mkConst<Rational>(1);
  Integer den = 1;
  for (std::uint64_t i = 1; i <= d; ++i)
  {
    num = nm->mkNode(Kind::MULT, num, t);
    den *= i;
    res =
        nm->mkNode(Kind::PLUS,
                   res,
                   nm->mkNode(Kind::DIVISION, num, nm->mkConst<Rational>(den)));
  }
  return Rewriter::rewrite(res);
}

/**
 * Evaluates an upper bound on the exponential function based on the Maclaurin
 * series. This approach is described in
 * https://dl.acm.org/doi/pdf/10.1145/3230639 Section 4.2.1.
 */
inline Node evalMaclaurinExpUpper(std::uint64_t d, TNode t)
{
  auto* nm = NodeManager::currentNM();
  Node f1 = evalMaclaurinExp(d - 1, t);
  Integer fac = 1;
  for (std::uint64_t i = 2; i <= d; ++i) fac *= i;
  Node f2 =
      nm->mkNode(Kind::PLUS,
                 nm->mkConst<Rational>(1),
                 nm->mkNode(Kind::DIVISION,
                            nm->mkNode(Kind::POW, t, nm->mkConst<Rational>(d)),
                            nm->mkConst<Rational>(fac)));
  return Rewriter::rewrite(nm->mkNode(Kind::MULT, f1, f2));
}

/**
 * Helper method to construct (t >= lb) AND (t <= up)
 */
Node mkBounds(TNode t, TNode lb, TNode ub)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkAnd(std::vector<Node>{nm->mkNode(Kind::GEQ, t, lb),
                                     nm->mkNode(Kind::LEQ, t, ub)});
}

/**
 * Helper method to construct a secant plane:
 * ((evall - evalu) / (l - u)) * (t - l) + evall
 */
Node mkSecant(TNode t, TNode l, TNode u, TNode evall, TNode evalu)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(Kind::PLUS,
                    nm->mkNode(Kind::MULT,
                               nm->mkNode(Kind::DIVISION,
                                          nm->mkNode(Kind::MINUS, evall, evalu),
                                          nm->mkNode(Kind::MINUS, l, u)),
                               nm->mkNode(Kind::MINUS, t, l)),
                    evall);
}

}  // namespace

void TranscendentalProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::ARITH_TRANS_PI, this);
  pc->registerChecker(PfRule::ARITH_TRANS_EXP_NEG, this);
  pc->registerChecker(PfRule::ARITH_TRANS_EXP_POSITIVITY, this);
  pc->registerChecker(PfRule::ARITH_TRANS_EXP_SUPER_LIN, this);
  pc->registerChecker(PfRule::ARITH_TRANS_EXP_ZERO, this);
  pc->registerChecker(PfRule::ARITH_TRANS_EXP_APPROX_ABOVE_POS, this);
  pc->registerChecker(PfRule::ARITH_TRANS_EXP_APPROX_ABOVE_NEG, this);
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_BOUNDS, this);
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_SHIFT, this);
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_SYMMETRY, this);
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_TANGENT_ZERO, this);
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_TANGENT_PI, this);
}

Node TranscendentalProofRuleChecker::checkInternal(
    PfRule id, const std::vector<Node>& children, const std::vector<Node>& args)
{
  NodeManager* nm = NodeManager::currentNM();
  auto zero = nm->mkConst<Rational>(0);
  auto one = nm->mkConst<Rational>(1);
  auto mone = nm->mkConst<Rational>(-1);
  auto pi = nm->mkNullaryOperator(nm->realType(), Kind::PI);
  auto mpi = nm->mkNode(Kind::MULT, mone, pi);
  Trace("nl-trans-checker") << "Checking " << id << std::endl;
  for (const auto& c : children)
  {
    Trace("nl-trans-checker") << "\t" << c << std::endl;
  }
  if (id == PfRule::ARITH_TRANS_PI)
  {
    Assert(children.empty());
    Assert(args.size() == 2);
    return nm->mkAnd(std::vector<Node>{nm->mkNode(Kind::GEQ, pi, args[0]),
                                       nm->mkNode(Kind::LEQ, pi, args[1])});
  }
  else if (id == PfRule::ARITH_TRANS_EXP_NEG)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node e = nm->mkNode(Kind::EXPONENTIAL, args[0]);
    return nm->mkNode(
        EQUAL, nm->mkNode(LT, args[0], zero), nm->mkNode(LT, e, one));
  }
  else if (id == PfRule::ARITH_TRANS_EXP_POSITIVITY)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node e = nm->mkNode(Kind::EXPONENTIAL, args[0]);
    return nm->mkNode(GT, e, zero);
  }
  else if (id == PfRule::ARITH_TRANS_EXP_SUPER_LIN)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node e = nm->mkNode(Kind::EXPONENTIAL, args[0]);
    return nm->mkNode(OR,
                      nm->mkNode(LEQ, args[0], zero),
                      nm->mkNode(GT, e, nm->mkNode(PLUS, args[0], one)));
  }
  else if (id == PfRule::ARITH_TRANS_EXP_ZERO)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node e = nm->mkNode(Kind::EXPONENTIAL, args[0]);
    return nm->mkNode(EQUAL, args[0].eqNode(zero), e.eqNode(one));
  }
  else if (id == PfRule::ARITH_TRANS_EXP_APPROX_ABOVE_POS)
  {
    Assert(children.empty());
    Assert(args.size() == 4);
    Assert(args[0].isConst() && args[0].getKind() == Kind::CONST_RATIONAL
           && args[0].getConst<Rational>().isIntegral());
    Assert(args[1].getType().isReal());
    Assert(args[2].isConst() && args[2].getKind() == Kind::CONST_RATIONAL);
    Assert(args[3].isConst() && args[3].getKind() == Kind::CONST_RATIONAL);
    std::uint64_t d =
        args[0].getConst<Rational>().getNumerator().toUnsignedInt();
    Node t = args[1];
    Node l = args[2];
    Node u = args[3];
    Node evall = evalMaclaurinExpUpper(d, l);
    Node evalu = evalMaclaurinExpUpper(d, u);
    Node evalsecant = mkSecant(t, l, u, evall, evalu);
    Node lem = nm->mkNode(
        Kind::IMPLIES,
        mkBounds(t, l, u),
        nm->mkNode(Kind::LEQ, nm->mkNode(Kind::EXPONENTIAL, t), evalsecant));
    return Rewriter::rewrite(lem);
  }
  else if (id == PfRule::ARITH_TRANS_EXP_APPROX_ABOVE_NEG)
  {
    Assert(children.empty());
    Assert(args.size() == 4);
    Assert(args[0].isConst() && args[0].getKind() == Kind::CONST_RATIONAL
           && args[0].getConst<Rational>().isIntegral());
    Assert(args[1].getType().isReal());
    Assert(args[2].isConst() && args[2].getKind() == Kind::CONST_RATIONAL);
    Assert(args[3].isConst() && args[3].getKind() == Kind::CONST_RATIONAL);
    std::uint64_t d =
        args[0].getConst<Rational>().getNumerator().toUnsignedInt();
    Node t = args[1];
    Node l = args[2];
    Node u = args[3];
    Node evall = evalMaclaurinExp(d, l);
    Node evalu = evalMaclaurinExp(d, u);
    Node evalsecant = mkSecant(t, l, u, evall, evalu);
    Node lem = nm->mkNode(
        Kind::IMPLIES,
        mkBounds(t, l, u),
        nm->mkNode(Kind::LEQ, nm->mkNode(Kind::EXPONENTIAL, t), evalsecant));
    return Rewriter::rewrite(lem);
  }
  else if (id == PfRule::ARITH_TRANS_SINE_BOUNDS)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getType().isReal());
    Node s = nm->mkNode(Kind::SINE, args[0]);
    return nm->mkNode(AND, nm->mkNode(LEQ, s, one), nm->mkNode(GEQ, s, mone));
  }
  else if (id == PfRule::ARITH_TRANS_SINE_SHIFT)
  {
    Assert(children.empty());
    Assert(args.size() == 3);
    const auto& x = args[0];
    const auto& y = args[1];
    const auto& s = args[2];
    return nm->mkAnd(std::vector<Node>{
        nm->mkAnd(std::vector<Node>{
            nm->mkNode(Kind::GEQ, y, nm->mkNode(Kind::MULT, mone, pi)),
            nm->mkNode(Kind::LEQ, y, pi)}),
        nm->mkNode(
            Kind::ITE,
            nm->mkAnd(std::vector<Node>{
                nm->mkNode(Kind::GEQ, x, nm->mkNode(Kind::MULT, mone, pi)),
                nm->mkNode(Kind::LEQ, x, pi),
            }),
            x.eqNode(y),
            x.eqNode(nm->mkNode(
                Kind::PLUS,
                y,
                nm->mkNode(Kind::MULT, nm->mkConst<Rational>(2), s, pi)))),
        nm->mkNode(Kind::SINE, y).eqNode(nm->mkNode(Kind::SINE, x))});
  }
  else if (id == PfRule::ARITH_TRANS_SINE_SYMMETRY)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getType().isReal());
    Node s1 = nm->mkNode(Kind::SINE, args[0]);
    Node s2 = nm->mkNode(
        Kind::SINE, Rewriter::rewrite(nm->mkNode(Kind::MULT, mone, args[0])));
    return nm->mkNode(PLUS, s1, s2).eqNode(zero);
  }
  else if (id == PfRule::ARITH_TRANS_SINE_TANGENT_ZERO)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getType().isReal());
    Node s = nm->mkNode(Kind::SINE, args[0]);
    return nm->mkNode(
        AND,
        nm->mkNode(
            IMPLIES, nm->mkNode(GT, args[0], zero), nm->mkNode(LT, s, args[0])),
        nm->mkNode(IMPLIES,
                   nm->mkNode(LT, args[0], zero),
                   nm->mkNode(GT, s, args[0])));
  }
  else if (id == PfRule::ARITH_TRANS_SINE_TANGENT_PI)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getType().isReal());
    Node s = nm->mkNode(Kind::SINE, args[0]);
    return nm->mkNode(
        AND,
        nm->mkNode(IMPLIES,
                   nm->mkNode(GT, args[0], mpi),
                   nm->mkNode(GT, s, nm->mkNode(MINUS, mpi, args[0]))),
        nm->mkNode(IMPLIES,
                   nm->mkNode(LT, args[0], pi),
                   nm->mkNode(LT, s, nm->mkNode(MINUS, pi, args[0]))));
  }
  return Node::null();
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
