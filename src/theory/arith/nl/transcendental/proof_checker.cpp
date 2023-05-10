/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "theory/arith/nl/transcendental/sine_solver.h"
#include "theory/arith/nl/transcendental/taylor_generator.h"
#include "theory/evaluator.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
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
 * evall + ((evall - evalu) / (l - u)) * (t - l)
 */
Node mkSecant(TNode t, TNode l, TNode u, TNode evall, TNode evalu)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(Kind::ADD,
                    evall,
                    nm->mkNode(Kind::MULT,
                               nm->mkNode(Kind::DIVISION,
                                          nm->mkNode(Kind::SUB, evall, evalu),
                                          nm->mkNode(Kind::SUB, l, u)),
                               nm->mkNode(Kind::SUB, t, l)));
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
  Node zero = nm->mkConstInt(Rational(0));
  Node one = nm->mkConstInt(Rational(1));
  Node mone = nm->mkConstInt(Rational(-1));
  Node pi = nm->mkNullaryOperator(nm->realType(), Kind::PI);
  Node mpi = nm->mkNode(Kind::MULT, mone, pi);
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
                      nm->mkNode(GT, e, nm->mkNode(ADD, args[0], one)));
  }
  else if (id == PfRule::ARITH_TRANS_EXP_ZERO)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node e = nm->mkNode(Kind::EXPONENTIAL, args[0]);
    Node rzero = nm->mkConstRealOrInt(args[0].getType(), Rational(0));
    Node rone = nm->mkConstReal(Rational(1));
    return nm->mkNode(EQUAL, args[0].eqNode(rzero), e.eqNode(rone));
  }
  else if (id == PfRule::ARITH_TRANS_EXP_APPROX_ABOVE_POS)
  {
    Assert(children.empty());
    Assert(args.size() == 4);
    Assert(args[0].isConst() && args[0].getType().isInteger());
    Assert(args[1].getType().isRealOrInt());
    Assert(args[2].isConst() && args[2].getType().isRealOrInt());
    Assert(args[3].isConst() && args[3].getType().isRealOrInt());
    std::uint64_t d =
        args[0].getConst<Rational>().getNumerator().toUnsignedInt();
    Node t = args[1];
    Node l = args[2];
    Node u = args[3];
    TaylorGenerator tg;
    TaylorGenerator::ApproximationBounds bounds;
    tg.getPolynomialApproximationBounds(Kind::EXPONENTIAL, d / 2, bounds);
    Evaluator eval(nullptr);
    Node evall = eval.eval(bounds.d_upperPos, {tg.getTaylorVariable()}, {l});
    Node evalu = eval.eval(bounds.d_upperPos, {tg.getTaylorVariable()}, {u});
    Node evalsecant = mkSecant(t, l, u, evall, evalu);
    Node lem = nm->mkNode(
        Kind::IMPLIES,
        mkBounds(t, l, u),
        nm->mkNode(Kind::LEQ, nm->mkNode(Kind::EXPONENTIAL, t), evalsecant));
    return lem;
  }
  else if (id == PfRule::ARITH_TRANS_EXP_APPROX_ABOVE_NEG)
  {
    Assert(children.empty());
    Assert(args.size() == 4);
    Assert(args[0].isConst() && args[0].getType().isInteger());
    Assert(args[1].getType().isRealOrInt());
    Assert(args[2].isConst() && args[2].getType().isRealOrInt());
    Assert(args[3].isConst() && args[3].getType().isRealOrInt());
    std::uint64_t d =
        args[0].getConst<Rational>().getNumerator().toUnsignedInt();
    Node t = args[1];
    Node l = args[2];
    Node u = args[3];
    TaylorGenerator tg;
    TaylorGenerator::ApproximationBounds bounds;
    tg.getPolynomialApproximationBounds(Kind::EXPONENTIAL, d / 2, bounds);
    Evaluator eval(nullptr);
    Node evall = eval.eval(bounds.d_upperNeg, {tg.getTaylorVariable()}, {l});
    Node evalu = eval.eval(bounds.d_upperNeg, {tg.getTaylorVariable()}, {u});
    Node evalsecant = mkSecant(t, l, u, evall, evalu);
    Node lem = nm->mkNode(
        Kind::IMPLIES,
        mkBounds(t, l, u),
        nm->mkNode(Kind::LEQ, nm->mkNode(Kind::EXPONENTIAL, t), evalsecant));
    return lem;
  }
  else if (id == PfRule::ARITH_TRANS_EXP_APPROX_BELOW)
  {
    Assert(children.empty());
    Assert(args.size() == 3);
    Assert(args[0].isConst() && args[0].getType().isInteger());
    Assert(args[1].isConst() && args[1].getType().isRealOrInt());
    Assert(args[2].getType().isRealOrInt());
    std::uint64_t d =
        args[0].getConst<Rational>().getNumerator().toUnsignedInt();
    Node c = args[1];
    Node t = args[2];
    TaylorGenerator tg;
    TaylorGenerator::ApproximationBounds bounds;
    tg.getPolynomialApproximationBoundForArg(Kind::EXPONENTIAL, c, d, bounds);
    Evaluator eval(nullptr);
    Node evalt = eval.eval(bounds.d_lower, {tg.getTaylorVariable()}, {c});
    return nm->mkNode(
        Kind::IMPLIES,
        nm->mkNode(Kind::GEQ, t, c),
        nm->mkNode(Kind::GEQ,
                   std::vector<Node>{nm->mkNode(Kind::EXPONENTIAL, t), evalt}));
  }
  else if (id == PfRule::ARITH_TRANS_SINE_BOUNDS)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getType().isRealOrInt());
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
    return SineSolver::getPhaseShiftLemma(x, y, s);
  }
  else if (id == PfRule::ARITH_TRANS_SINE_SYMMETRY)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getType().isRealOrInt());
    Node s1 = nm->mkNode(Kind::SINE, args[0]);
    Node s2 = nm->mkNode(Kind::SINE, nm->mkNode(Kind::MULT, mone, args[0]));
    return nm->mkNode(ADD, s1, s2).eqNode(zero);
  }
  else if (id == PfRule::ARITH_TRANS_SINE_TANGENT_ZERO)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getType().isRealOrInt());
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
    Assert(args[0].getType().isRealOrInt());
    Node s = nm->mkNode(Kind::SINE, args[0]);
    return nm->mkNode(
        AND,
        nm->mkNode(IMPLIES,
                   nm->mkNode(GT, args[0], mpi),
                   nm->mkNode(GT, s, nm->mkNode(SUB, mpi, args[0]))),
        nm->mkNode(IMPLIES,
                   nm->mkNode(LT, args[0], pi),
                   nm->mkNode(LT, s, nm->mkNode(SUB, pi, args[0]))));
  }
  else if (id == PfRule::ARITH_TRANS_SINE_APPROX_ABOVE_NEG)
  {
    Assert(children.empty());
    Assert(args.size() == 6);
    Assert(args[0].isConst() && args[0].getType().isInteger());
    Assert(args[1].getType().isRealOrInt());
    Assert(args[2].getType().isRealOrInt());
    Assert(args[3].getType().isRealOrInt());
    Assert(args[4].isConst() && args[4].getType().isRealOrInt());
    Assert(args[5].isConst() && args[5].getType().isRealOrInt());
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
    Evaluator eval(nullptr);
    Node evall = eval.eval(bounds.d_upperNeg, {tg.getTaylorVariable()}, {l});
    Node evalu = eval.eval(bounds.d_upperNeg, {tg.getTaylorVariable()}, {u});
    Node lem = nm->mkNode(
        Kind::IMPLIES,
        mkBounds(t, lb, ub),
        nm->mkNode(
            Kind::LEQ, nm->mkNode(Kind::SINE, t), mkSecant(t, lb, ub, l, u)));
    return lem;
  }
  else if (id == PfRule::ARITH_TRANS_SINE_APPROX_ABOVE_POS)
  {
    Assert(children.empty());
    Assert(args.size() == 5);
    Assert(args[0].isConst() && args[0].getType().isInteger());
    Assert(args[1].getType().isRealOrInt());
    Assert(args[2].getType().isRealOrInt());
    Assert(args[3].getType().isRealOrInt());
    std::uint64_t d =
        args[0].getConst<Rational>().getNumerator().toUnsignedInt();
    Node t = args[1];
    Node c = args[2];
    Node lb = args[3];
    Node ub = args[4];
    TaylorGenerator tg;
    TaylorGenerator::ApproximationBounds bounds;
    tg.getPolynomialApproximationBounds(Kind::SINE, d / 2, bounds);
    Evaluator eval(nullptr);
    Node evalc = eval.eval(bounds.d_upperPos, {tg.getTaylorVariable()}, {c});
    return nm->mkNode(Kind::IMPLIES,
                      mkBounds(t, lb, ub),
                      nm->mkNode(Kind::LEQ, nm->mkNode(Kind::SINE, t), evalc));
  }
  else if (id == PfRule::ARITH_TRANS_SINE_APPROX_BELOW_POS)
  {
    Assert(children.empty());
    Assert(args.size() == 6);
    Assert(args[0].isConst() && args[0].getType().isInteger());
    Assert(args[1].getType().isRealOrInt());
    Assert(args[2].getType().isRealOrInt());
    Assert(args[3].getType().isRealOrInt());
    Assert(args[4].isConst() && args[4].getType().isRealOrInt());
    Assert(args[5].isConst() && args[5].getType().isRealOrInt());
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
    Evaluator eval(nullptr);
    Node evall = eval.eval(bounds.d_lower, {tg.getTaylorVariable()}, {l});
    Node evalu = eval.eval(bounds.d_lower, {tg.getTaylorVariable()}, {u});
    Node lem = nm->mkNode(
        Kind::IMPLIES,
        mkBounds(t, lb, ub),
        nm->mkNode(
            Kind::GEQ, nm->mkNode(Kind::SINE, t), mkSecant(t, lb, ub, l, u)));
    return lem;
  }
  else if (id == PfRule::ARITH_TRANS_SINE_APPROX_BELOW_NEG)
  {
    Assert(children.empty());
    Assert(args.size() == 5);
    Assert(args[0].isConst() && args[0].getType().isInteger());
    Assert(args[1].getType().isRealOrInt());
    Assert(args[2].getType().isRealOrInt());
    Assert(args[3].getType().isRealOrInt());
    std::uint64_t d =
        args[0].getConst<Rational>().getNumerator().toUnsignedInt();
    Node t = args[1];
    Node c = args[2];
    Node lb = args[3];
    Node ub = args[4];
    TaylorGenerator tg;
    TaylorGenerator::ApproximationBounds bounds;
    tg.getPolynomialApproximationBounds(Kind::SINE, d / 2, bounds);
    Evaluator eval(nullptr);
    Node evalc = eval.eval(bounds.d_lower, {tg.getTaylorVariable()}, {c});
    return nm->mkNode(Kind::IMPLIES,
                      mkBounds(t, lb, ub),
                      nm->mkNode(Kind::GEQ, nm->mkNode(Kind::SINE, t), evalc));
  }
  return Node::null();
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
