/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof checker for transcendentals.
 */

#include "theory/arith/nl/transcendental/proof_checker.h"

#include "expr/sequence.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/nl/transcendental/taylor_generator.h"
#include "theory/rewriter.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

namespace {

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
  pc->registerChecker(PfRule::ARITH_TRANS_EXP_APPROX_BELOW, this);
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_BOUNDS, this);
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_SHIFT, this);
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_SYMMETRY, this);
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_TANGENT_ZERO, this);
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_TANGENT_PI, this);
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_APPROX_BELOW_POS, this);
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_APPROX_BELOW_NEG, this);
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_APPROX_ABOVE_POS, this);
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_APPROX_ABOVE_NEG, this);
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
  Trace("nl-trans-checker") << "Children:" << std::endl;
  for (const auto& c : children)
  {
    Trace("nl-trans-checker") << "\t" << c << std::endl;
  }
  Trace("nl-trans-checker") << "Args:" << std::endl;
  for (const auto& a : args)
  {
    Trace("nl-trans-checker") << "\t" << a << std::endl;
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
    TaylorGenerator tg;
    TaylorGenerator::ApproximationBounds bounds;
    tg.getPolynomialApproximationBounds(Kind::EXPONENTIAL, d / 2, bounds);
    Node evall = Rewriter::rewrite(
        bounds.d_upperPos.substitute(tg.getTaylorVariable(), l));
    Node evalu = Rewriter::rewrite(
        bounds.d_upperPos.substitute(tg.getTaylorVariable(), u));
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
    TaylorGenerator tg;
    TaylorGenerator::ApproximationBounds bounds;
    tg.getPolynomialApproximationBounds(Kind::EXPONENTIAL, d / 2, bounds);
    Node evall = Rewriter::rewrite(
        bounds.d_upperNeg.substitute(tg.getTaylorVariable(), l));
    Node evalu = Rewriter::rewrite(
        bounds.d_upperNeg.substitute(tg.getTaylorVariable(), u));
    Node evalsecant = mkSecant(t, l, u, evall, evalu);
    Node lem = nm->mkNode(
        Kind::IMPLIES,
        mkBounds(t, l, u),
        nm->mkNode(Kind::LEQ, nm->mkNode(Kind::EXPONENTIAL, t), evalsecant));
    return Rewriter::rewrite(lem);
  }
  else if (id == PfRule::ARITH_TRANS_EXP_APPROX_BELOW)
  {
    Assert(children.empty());
    Assert(args.size() == 2);
    Assert(args[0].isConst() && args[0].getKind() == Kind::CONST_RATIONAL
           && args[0].getConst<Rational>().isIntegral());
    Assert(args[1].getType().isReal());
    std::uint64_t d =
        args[0].getConst<Rational>().getNumerator().toUnsignedInt();
    Node t = args[1];
    TaylorGenerator tg;
    TaylorGenerator::ApproximationBounds bounds;
    tg.getPolynomialApproximationBounds(Kind::EXPONENTIAL, d, bounds);
    Node eval =
        Rewriter::rewrite(bounds.d_lower.substitute(tg.getTaylorVariable(), t));
    return nm->mkNode(
        Kind::GEQ, std::vector<Node>{nm->mkNode(Kind::EXPONENTIAL, t), eval});
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
  else if (id == PfRule::ARITH_TRANS_SINE_APPROX_ABOVE_NEG)
  {
    Assert(children.empty());
    Assert(args.size() == 6);
    Assert(args[0].isConst() && args[0].getKind() == Kind::CONST_RATIONAL
           && args[0].getConst<Rational>().isIntegral());
    Assert(args[1].getType().isReal());
    Assert(args[2].getType().isReal());
    Assert(args[3].getType().isReal());
    Assert(args[4].isConst() && args[4].getKind() == Kind::CONST_RATIONAL);
    Assert(args[5].isConst() && args[5].getKind() == Kind::CONST_RATIONAL);
    std::uint64_t d =
        args[0].getConst<Rational>().getNumerator().toUnsignedInt();
    Node t = args[1];
    Node lb = args[2];
    Node ub = args[3];
    Node l = args[4];
    Node u = args[5];
    TaylorGenerator tg;
    TaylorGenerator::ApproximationBounds bounds;
    tg.getPolynomialApproximationBounds(Kind::SINE, d / 2, bounds);
    Node evall = Rewriter::rewrite(
        bounds.d_upperNeg.substitute(tg.getTaylorVariable(), l));
    Node evalu = Rewriter::rewrite(
        bounds.d_upperNeg.substitute(tg.getTaylorVariable(), u));
    Node lem = nm->mkNode(
        Kind::IMPLIES,
        mkBounds(t, lb, ub),
        nm->mkNode(
            Kind::LEQ, nm->mkNode(Kind::SINE, t), mkSecant(t, lb, ub, l, u)));
    return Rewriter::rewrite(lem);
  }
  else if (id == PfRule::ARITH_TRANS_SINE_APPROX_ABOVE_POS)
  {
    Assert(children.empty());
    Assert(args.size() == 5);
    Assert(args[0].isConst() && args[0].getKind() == Kind::CONST_RATIONAL
           && args[0].getConst<Rational>().isIntegral());
    Assert(args[1].getType().isReal());
    Assert(args[2].getType().isReal());
    Assert(args[3].getType().isReal());
    std::uint64_t d =
        args[0].getConst<Rational>().getNumerator().toUnsignedInt();
    Node t = args[1];
    Node c = args[2];
    Node lb = args[3];
    Node ub = args[4];
    TaylorGenerator tg;
    TaylorGenerator::ApproximationBounds bounds;
    tg.getPolynomialApproximationBounds(Kind::SINE, d / 2, bounds);
    Node eval = Rewriter::rewrite(
        bounds.d_upperPos.substitute(tg.getTaylorVariable(), c));
    return Rewriter::rewrite(
        nm->mkNode(Kind::IMPLIES,
                   mkBounds(t, lb, ub),
                   nm->mkNode(Kind::LEQ, nm->mkNode(Kind::SINE, t), eval)));
  }
  else if (id == PfRule::ARITH_TRANS_SINE_APPROX_BELOW_POS)
  {
    Assert(children.empty());
    Assert(args.size() == 6);
    Assert(args[0].isConst() && args[0].getKind() == Kind::CONST_RATIONAL
           && args[0].getConst<Rational>().isIntegral());
    Assert(args[1].getType().isReal());
    Assert(args[2].getType().isReal());
    Assert(args[3].getType().isReal());
    Assert(args[4].isConst() && args[4].getKind() == Kind::CONST_RATIONAL);
    Assert(args[5].isConst() && args[5].getKind() == Kind::CONST_RATIONAL);
    std::uint64_t d =
        args[0].getConst<Rational>().getNumerator().toUnsignedInt();
    Node t = args[1];
    Node lb = args[2];
    Node ub = args[3];
    Node l = args[4];
    Node u = args[5];
    TaylorGenerator tg;
    TaylorGenerator::ApproximationBounds bounds;
    tg.getPolynomialApproximationBounds(Kind::SINE, d / 2, bounds);
    Node evall =
        Rewriter::rewrite(bounds.d_lower.substitute(tg.getTaylorVariable(), l));
    Node evalu =
        Rewriter::rewrite(bounds.d_lower.substitute(tg.getTaylorVariable(), u));
    Node lem = nm->mkNode(
        Kind::IMPLIES,
        mkBounds(t, lb, ub),
        nm->mkNode(
            Kind::GEQ, nm->mkNode(Kind::SINE, t), mkSecant(t, lb, ub, l, u)));
    return Rewriter::rewrite(lem);
  }
  else if (id == PfRule::ARITH_TRANS_SINE_APPROX_BELOW_NEG)
  {
    Assert(children.empty());
    Assert(args.size() == 5);
    Assert(args[0].isConst() && args[0].getKind() == Kind::CONST_RATIONAL
           && args[0].getConst<Rational>().isIntegral());
    Assert(args[1].getType().isReal());
    Assert(args[2].getType().isReal());
    Assert(args[3].getType().isReal());
    std::uint64_t d =
        args[0].getConst<Rational>().getNumerator().toUnsignedInt();
    Node t = args[1];
    Node c = args[2];
    Node lb = args[3];
    Node ub = args[4];
    TaylorGenerator tg;
    TaylorGenerator::ApproximationBounds bounds;
    tg.getPolynomialApproximationBounds(Kind::SINE, d / 2, bounds);
    Node eval =
        Rewriter::rewrite(bounds.d_lower.substitute(tg.getTaylorVariable(), c));
    return Rewriter::rewrite(
        nm->mkNode(Kind::IMPLIES,
                   mkBounds(t, lb, ub),
                   nm->mkNode(Kind::GEQ, nm->mkNode(Kind::SINE, t), eval)));
  }
  return Node::null();
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
