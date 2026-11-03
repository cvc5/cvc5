/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for lia star utilities.
 */

#ifdef CVC5_USE_NORMALIZ

#include <vector>

#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "expr/skolem_manager.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "test_smt.h"
#include "theory/arith/liastar/liastar_utils.h"
#include "util/bitvector.h"
#include "util/rational.h"

namespace cvc5::internal {

using namespace theory;
using namespace theory::arith;
using namespace theory::arith::liastar;

namespace test {

class TestLiaStarUtils : public TestSmt
{
 protected:
  TypeNode intType;
  Node zero, one, two, x, y;
  NodeManager* nm;
  Env* e;

  void SetUp() override
  {
    TestSmt::SetUp();
    d_slvEngine->setOption("dag-thresh", "0", true);
    nm = d_nodeManager.get();
    e = &d_slvEngine->getEnv();
    intType = nm->integerType();
    zero = nm->mkConstInt(Rational(0));
    one = nm->mkConstInt(Rational(1));
    two = nm->mkConstInt(Rational(2));
    x = nm->mkBoundVar("x", intType);
    y = nm->mkBoundVar("y", intType);
  }

  Node boundVarList(const std::vector<Node>& vars)
  {
    return nm->mkNode(Kind::BOUND_VAR_LIST, vars);
  }

  Node lambda(const std::vector<Node>& vars, Node body)
  {
    return nm->mkNode(Kind::LAMBDA, boundVarList(vars), body);
  }

  Node boolVar(const std::string& name)
  {
    return nm->mkBoundVar(name, nm->booleanType());
  }

  /** Whether a and b agree for all values of their free variables. */
  bool isEquivalent(Node a, Node b)
  {
    // (exists (vars) (distinct a b)) is unsat iff a and b are equivalent
    Node distinct = a.eqNode(b).notNode();
    std::unordered_set<Node> fvs;
    expr::getFreeVariables(distinct, fvs);
    std::vector<Node> vars(fvs.begin(), fvs.end());
    return LiaStarUtils::cvc5CheckSat(vars, distinct, *e).getStatus()
           == Result::Status::UNSAT;
  }
};

TEST_F(TestLiaStarUtils, getVectorPredicateInstantiatesLambda)
{
  Node u = nm->mkBoundVar("u", intType);
  Node v = nm->mkBoundVar("v", intType);
  // (int.star-contains (lambda ((u Int) (v Int)) (>= u v)) x y)
  Node star = nm->mkNode(
      Kind::STAR_CONTAINS, lambda({u, v}, nm->mkNode(Kind::GEQ, u, v)), x, y);

  auto [predicate, nonnegative] = LiaStarUtils::getVectorPredicate(star, nm);

  ASSERT_EQ(nm->mkNode(Kind::GEQ, x, y), predicate);
  ASSERT_EQ("(and (and true (>= x 0)) (>= y 0))", nonnegative.toString());
}

TEST_F(TestLiaStarUtils, getVectorPredicateAcceptsConstantLambda)
{
  Node u = nm->mkBoundVar("u", intType);
  // (int.star-contains (lambda ((u Int)) false) x), where the rewriter
  // normalizes the constant lambda to a function array constant
  Node constantLambda =
      e->getRewriter()->rewrite(lambda({u}, nm->mkConst<bool>(false)));
  Node star = nm->mkNode(Kind::STAR_CONTAINS, constantLambda, x);

  auto [predicate, nonnegative] = LiaStarUtils::getVectorPredicate(star, nm);

  ASSERT_EQ(nm->mkConst<bool>(false), predicate);
  ASSERT_EQ("(and true (>= x 0))", nonnegative.toString());
}

TEST_F(TestLiaStarUtils, getVectorPredicateAcceptsLiftedLambda)
{
  Node u = nm->mkBoundVar("u", intType);
  // (int.star-contains k x), where lambda lifting replaced the lambda
  // (lambda ((u Int)) (>= u 1)) by its purification skolem k
  Node lifted =
      SkolemManager::mkPurifySkolem(lambda({u}, nm->mkNode(Kind::GEQ, u, one)));
  Node star = nm->mkNode(Kind::STAR_CONTAINS, lifted, x);

  auto [predicate, nonnegative] = LiaStarUtils::getVectorPredicate(star, nm);

  ASSERT_EQ(nm->mkNode(Kind::GEQ, x, one), predicate);
  ASSERT_EQ("(and true (>= x 0))", nonnegative.toString());
}

TEST_F(TestLiaStarUtils, getMatricesConjunctionIsOneMatrix)
{
  // (and (>= x 1) (= y 0)) over the coordinates (x y)
  Node conjunction = nm->mkNode(Kind::AND,
                                nm->mkNode(Kind::GEQ, x, one),
                                nm->mkNode(Kind::EQUAL, y, zero));

  auto matrices = LiaStarUtils::getMatrices(boundVarList({x, y}), conjunction);

  ASSERT_EQ(1, matrices.size());
  ASSERT_EQ(std::vector<std::string>({"x[1] >= 1;", "x[2] = 0;"}),
            matrices[0].first);
}

TEST_F(TestLiaStarUtils, getMatricesDisjunctionIsOneMatrixPerDisjunct)
{
  // (or (>= x 1) (>= y 2))
  Node disjunction = nm->mkNode(
      Kind::OR, nm->mkNode(Kind::GEQ, x, one), nm->mkNode(Kind::GEQ, y, two));

  auto matrices = LiaStarUtils::getMatrices(boundVarList({x, y}), disjunction);

  ASSERT_EQ(2, matrices.size());
  ASSERT_EQ(std::vector<std::string>({"x[1] >= 1;"}), matrices[0].first);
  ASSERT_EQ(std::vector<std::string>({"x[2] >= 2;"}), matrices[1].first);
}

TEST_F(TestLiaStarUtils, getMatricesPrintsCoefficients)
{
  // (>= (+ (* 2 x) y) 1)
  Node sum = nm->mkNode(Kind::ADD, nm->mkNode(Kind::MULT, two, x), y);
  Node constraint = nm->mkNode(Kind::GEQ, sum, one);

  auto matrices = LiaStarUtils::getMatrices(boundVarList({x, y}), constraint);

  ASSERT_EQ(1, matrices.size());
  ASSERT_EQ(std::vector<std::string>({"2x[1] + x[2] >= 1;"}),
            matrices[0].first);
}

TEST_F(TestLiaStarUtils, getMatricesPrintsNegativeCoefficients)
{
  // (>= (+ (* 2 x) (* (- 1) y)) 5)
  Node minusOne = nm->mkConstInt(Rational(-1));
  Node five = nm->mkConstInt(Rational(5));
  Node sum = nm->mkNode(Kind::ADD,
                        nm->mkNode(Kind::MULT, two, x),
                        nm->mkNode(Kind::MULT, minusOne, y));
  Node constraint = nm->mkNode(Kind::GEQ, sum, five);

  auto matrices = LiaStarUtils::getMatrices(boundVarList({x, y}), constraint);

  ASSERT_EQ(1, matrices.size());
  ASSERT_EQ(std::vector<std::string>({"2x[1] - x[2] >= 5;"}),
            matrices[0].first);
}

TEST_F(TestLiaStarUtils, getMatricesPrintsRelationsAndKeepsDisjuncts)
{
  // (or (< x y) (> x y) (<= x y)), one matrix per relation
  Node disjunction = nm->mkNode(Kind::OR,
                                nm->mkNode(Kind::LT, x, y),
                                nm->mkNode(Kind::GT, x, y),
                                nm->mkNode(Kind::LEQ, x, y));

  auto matrices = LiaStarUtils::getMatrices(boundVarList({x, y}), disjunction);

  ASSERT_EQ(3, matrices.size());
  ASSERT_EQ(std::vector<std::string>({"x[1] < x[2];"}), matrices[0].first);
  ASSERT_EQ(std::vector<std::string>({"x[1] > x[2];"}), matrices[1].first);
  ASSERT_EQ(std::vector<std::string>({"x[1] <= x[2];"}), matrices[2].first);
  // each pair carries its own disjunct
  for (size_t i = 0; i < 3; i++)
  {
    ASSERT_EQ(disjunction[i], matrices[i].second);
  }
}

TEST_F(TestLiaStarUtils, getMatricesConstants)
{
  // Normaliz needs at least one constraint, so true becomes a tautology and
  // false a contradiction
  Node vars = boundVarList({x});
  auto trueMatrices = LiaStarUtils::getMatrices(vars, nm->mkConst<bool>(true));
  auto falseMatrices =
      LiaStarUtils::getMatrices(vars, nm->mkConst<bool>(false));

  ASSERT_EQ(1, trueMatrices.size());
  ASSERT_EQ(std::vector<std::string>({"x[1] = x[1];"}), trueMatrices[0].first);
  ASSERT_EQ(1, falseMatrices.size());
  ASSERT_EQ(std::vector<std::string>({"1 = 0;"}), falseMatrices[0].first);
}

TEST_F(TestLiaStarUtils, getMatricesRejectsCapturedConstants)
{
  // (= x (* 2 a)) for a constant a has no Normaliz constraint over (x):
  // dropping a would give x[1] = 2, so (lambda ((x Int)) (= x (* 2 a)))
  // would be reduced as {2}* rather than {2a}*
  Node a = nm->mkVar("a", intType);
  Node twoA = nm->mkNode(Kind::MULT, two, a);
  Node equality = x.eqNode(twoA);
  Node constraint = e->getRewriter()->rewrite(equality);
  Node vars = boundVarList({x});

  ASSERT_THROW(LiaStarUtils::getMatrices(vars, constraint), LogicException);
  // the Normaliz subsolver translates its queries with getMatrices too
  ASSERT_THROW(LiaStarUtils::normalizCheckSat(vars, constraint, false),
               LogicException);
}

TEST_F(TestLiaStarUtils, getMatricesRejectsNonlinearTerms)
{
  // (>= (* x y) 1) and (>= (mod x 2) 1) over (x y)
  Node product = nm->mkNode(Kind::MULT, x, y);
  Node productAtom = nm->mkNode(Kind::GEQ, product, one);
  Node nonlinear = e->getRewriter()->rewrite(productAtom);
  Node mod = nm->mkNode(Kind::INTS_MODULUS, x, two);
  Node modulus = nm->mkNode(Kind::GEQ, mod, one);
  Node vars = boundVarList({x, y});

  ASSERT_THROW(LiaStarUtils::getMatrices(vars, nonlinear), LogicException);
  ASSERT_THROW(LiaStarUtils::getMatrices(vars, modulus), LogicException);
}

TEST_F(TestLiaStarUtils, getMatricesRejectsBooleanAtoms)
{
  // p has no Normaliz constraint: dropping it would reduce
  // (lambda ((x Int)) p) as if p were false
  Node p = boolVar("p");
  Node notP = p.notNode();
  Node atLeastOne = nm->mkNode(Kind::GEQ, x, one);
  Node conjunction = nm->mkNode(Kind::AND, p, atLeastOne);
  Node equality = p.eqNode(atLeastOne);
  Node vars = boundVarList({x});

  ASSERT_THROW(LiaStarUtils::getMatrices(vars, p), LogicException);
  ASSERT_THROW(LiaStarUtils::getMatrices(vars, notP), LogicException);
  ASSERT_THROW(LiaStarUtils::getMatrices(vars, conjunction), LogicException);
  ASSERT_THROW(LiaStarUtils::getMatrices(vars, equality), LogicException);
}

TEST_F(TestLiaStarUtils, getMatricesRejectsTermsOfOtherTypes)
{
  // (= b #x00) for a bit-vector b and (>= x r) for a real r have no Normaliz
  // constraint over the integer coordinates (x)
  Node b = nm->mkVar("b", nm->mkBitVectorType(8));
  Node zeroByte = nm->mkConst(BitVector(8, 0u));
  Node bitVectorEquality = b.eqNode(zeroByte);
  Node r = nm->mkVar("r", nm->realType());
  Node atLeastR = nm->mkNode(Kind::GEQ, x, r);
  Node realConstraint = e->getRewriter()->rewrite(atLeastR);
  Node vars = boundVarList({x});

  ASSERT_THROW(LiaStarUtils::getMatrices(vars, bitVectorEquality),
               LogicException);
  ASSERT_THROW(LiaStarUtils::getMatrices(vars, realConstraint), LogicException);
}

TEST_F(TestLiaStarUtils, cvc5CheckSatUnsat)
{
  // exists x. x >= 1 and x <= 0
  Node assertion = nm->mkNode(
      Kind::AND, nm->mkNode(Kind::GEQ, x, one), nm->mkNode(Kind::LEQ, x, zero));

  Result result = LiaStarUtils::cvc5CheckSat({x}, assertion, *e);

  ASSERT_EQ(Result::Status::UNSAT, result.getStatus());
}

TEST_F(TestLiaStarUtils, cvc5CheckSatSat)
{
  // exists x. x >= 1
  Node assertion = nm->mkNode(Kind::GEQ, x, one);

  Result result = LiaStarUtils::cvc5CheckSat({x}, assertion, *e);

  ASSERT_EQ(Result::Status::SAT, result.getStatus());
}

TEST_F(TestLiaStarUtils, areAssertionsUnsatConjoinsAssertions)
{
  // x >= 1 and x <= 0 are unsat together, satisfiable apart
  Node lower = nm->mkNode(Kind::GEQ, x, one);
  Node upper = nm->mkNode(Kind::LEQ, x, zero);

  ASSERT_EQ(Result::Status::UNSAT,
            LiaStarUtils::areAssertionsUnsat({lower, upper}, *e).getStatus());
  ASSERT_EQ(Result::Status::SAT,
            LiaStarUtils::areAssertionsUnsat({lower}, *e).getStatus());
}

TEST_F(TestLiaStarUtils, areAssertionsUnsatIsNoneWhenSubsolverIsDisabled)
{
  d_slvEngine->setOption("arith-liastar-subsolver", "false", true);
  Node lower = nm->mkNode(Kind::GEQ, x, one);
  Node upper = nm->mkNode(Kind::LEQ, x, zero);

  Result result = LiaStarUtils::areAssertionsUnsat({lower, upper}, *e);

  ASSERT_EQ(Result::Status::NONE, result.getStatus());
}

TEST_F(TestLiaStarUtils, normalizCheckSatEmptyConeIsUnsat)
{
  // x >= 1 and x <= 0 describe an empty cone
  Node assertion = nm->mkNode(
      Kind::AND, nm->mkNode(Kind::GEQ, x, one), nm->mkNode(Kind::LEQ, x, zero));

  Result result =
      LiaStarUtils::normalizCheckSat(boundVarList({x}), assertion, false);

  ASSERT_EQ(Result::Status::UNSAT, result.getStatus());
}

TEST_F(TestLiaStarUtils, normalizCheckSatNonemptyConeIsNone)
{
  // x >= 1 describes a nonempty cone, which is reported as none rather
  // than sat
  Node assertion = nm->mkNode(Kind::GEQ, x, one);

  Result result =
      LiaStarUtils::normalizCheckSat(boundVarList({x}), assertion, false);

  ASSERT_EQ(Result::Status::NONE, result.getStatus());
}

TEST_F(TestLiaStarUtils, normalizCheckSatAssumeNonnegative)
{
  // x <= -1 is satisfiable over the integers, but not over the
  // nonnegative orthant
  Node assertion = nm->mkNode(Kind::LEQ, x, nm->mkConstInt(Rational(-1)));

  ASSERT_EQ(Result::Status::NONE,
            LiaStarUtils::normalizCheckSat(boundVarList({x}), assertion, false)
                .getStatus());
  ASSERT_EQ(Result::Status::UNSAT,
            LiaStarUtils::normalizCheckSat(boundVarList({x}), assertion, true)
                .getStatus());
}

TEST_F(TestLiaStarUtils, distribute1)
{
  Node a = boolVar("a"), b = boolVar("b"), f = boolVar("f"), g = boolVar("g");
  Node u = boolVar("u"), v = boolVar("v"), p = boolVar("p"), q = boolVar("q");
  Node z = boolVar("z");
  // (and
  //   (or
  //     (and
  //        (or f g)
  //        (or p q))
  //      z)
  //     (or u v)
  //   (and a b)
  //  )

  Node or_fg = nm->mkNode(Kind::OR, {f, g});
  Node or_xy = nm->mkNode(Kind::OR, {p, q});
  Node or_uv = nm->mkNode(Kind::OR, {u, v});
  Node and_ab = nm->mkNode(Kind::AND, {a, b});
  Node and_or_fg_or_xy = nm->mkNode(Kind::AND, {or_fg, or_xy});
  Node and_z = nm->mkNode(Kind::AND, {and_or_fg_or_xy, z});
  Node or_uv_z = nm->mkNode(Kind::OR, {or_uv, and_z});
  Node and_outer = nm->mkNode(Kind::AND, {or_uv_z, and_ab});
  Node dnf = LiaStarUtils::distribute(and_outer, *e);
  dnf = LiaStarUtils::recursiveFlatten(nm, dnf);
  ASSERT_EQ(
      "(or (and a b u) (and a b v) (and a b z f p) (and a b z g p) (and a b z "
      "f q) (and a b z g q))",
      dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF1)
{
  // (not (>= (+ (* 3 x) (* (- 1) y)) 9)), i.e., not (3*x - y >= 9)
  Node three = nm->mkConstInt(Rational(3));
  Node nine = nm->mkConstInt(Rational(9));

  Node threeTimesX = nm->mkNode(Kind::MULT, three, x);
  Node minus = nm->mkNode(Kind::SUB, threeTimesX, y);
  Node geq = nm->mkNode(Kind::GEQ, minus, nine);
  Node notGEQ = geq.notNode();
  Node dnf = LiaStarUtils::toDNF(notGEQ, *e);
  ASSERT_EQ("(< (- (* 3 x) y) 9)", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF2)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  // (and (or a b) (or c d))
  Node or_a_b = a.orNode(b);
  Node or_c_d = c.orNode(d);
  Node and = or_a_b.andNode(or_c_d);
  Node dnf = LiaStarUtils::toDNF(and, *e);
  ASSERT_EQ("(or (and a c) (and b c) (and a d) (and b d))", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF3)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  Node p = boolVar("p");
  // (and (or (and a p) b) (or c d))
  Node and_a_x = a.andNode(p);
  Node or_a_b = and_a_x.orNode(b);
  Node or_c_d = c.orNode(d);
  Node and = or_a_b.andNode(or_c_d);
  Node dnf = LiaStarUtils::toDNF(and, *e);
  ASSERT_EQ("(or (and a p c) (and b c) (and a p d) (and b d))", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF4)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  Node p = boolVar("p");
  // (and (or a (and b p)) (or c d))
  Node and_b_x = b.andNode(p);
  Node or_a_b = a.orNode(and_b_x);
  Node or_c_d = c.orNode(d);
  Node and = or_a_b.andNode(or_c_d);
  Node dnf = LiaStarUtils::toDNF(and, *e);
  ASSERT_EQ("(or (and a c) (and b p c) (and a d) (and b p d))", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF5)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  Node p = boolVar("p");
  // (and (or a b p) (or c d))
  Node or1 = nm->mkNode(Kind::OR, {a, b, p});
  Node or2 = nm->mkNode(Kind::OR, {c, d});
  Node and = or1.andNode(or2);
  Node dnf = LiaStarUtils::toDNF(and, *e);
  ASSERT_EQ("(or (and a c) (and b c) (and p c) (and a d) (and b d) (and p d))",
            dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF6)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  Node p = boolVar("p"), q = boolVar("q");
  // (and (or a b) (or c d) (or p q))
  Node or1 = nm->mkNode(Kind::OR, {a, b});
  Node or2 = nm->mkNode(Kind::OR, {c, d});
  Node or3 = nm->mkNode(Kind::OR, {p, q});
  Node and = nm->mkNode(Kind::AND, {or1, or2, or3});
  Node dnf = LiaStarUtils::toDNF(and, *e);
  ASSERT_EQ(
      "(or (and a c p) (and b c p) (and a d p) (and b d p) (and a c q) (and b "
      "c q) (and a d q) (and b d q))",
      dnf.toString());
}

TEST_F(TestLiaStarUtils, removeItesUnderUnaryMinus)
{
  Node c = boolVar("c");
  // (>= (- (ite c x y)) 1): the ite below the unary minus is removed too
  Node neg = nm->mkNode(Kind::NEG, nm->mkNode(Kind::ITE, c, x, y));
  Node dnf = LiaStarUtils::toDNF(nm->mkNode(Kind::GEQ, neg, one), *e);
  ASSERT_FALSE(expr::hasSubtermKind(Kind::ITE, dnf)) << dnf;
  // one disjunct per branch, guarded by c and (not c)
  ASSERT_EQ(Kind::OR, dnf.getKind());
  ASSERT_EQ(2, dnf.getNumChildren());
}

TEST_F(TestLiaStarUtils, removeNotKeepsNegatedBooleanVariables)
{
  Node p = boolVar("p"), q = boolVar("q");
  // (not (and p q)): the literals have no relation to flip
  Node dnf = LiaStarUtils::toDNF(p.andNode(q).notNode(), *e);
  ASSERT_EQ("(or (not p) (not q))", dnf.toString());
}

TEST_F(TestLiaStarUtils, removeNotFlipsNegatedConstraints)
{
  // (not (and (< x y) (> x y) (<= x y) (>= x y) (= x y)))
  Node conjunction = nm->mkNode(Kind::AND,
                                {nm->mkNode(Kind::LT, x, y),
                                 nm->mkNode(Kind::GT, x, y),
                                 nm->mkNode(Kind::LEQ, x, y),
                                 nm->mkNode(Kind::GEQ, x, y),
                                 nm->mkNode(Kind::EQUAL, x, y)});

  Node nnf = LiaStarUtils::removeNot(conjunction.notNode(), *e);

  ASSERT_EQ("(or (>= x y) (<= x y) (> x y) (< x y) (or (> x y) (< x y)))",
            nnf.toString());
}

TEST_F(TestLiaStarUtils, removeNotExpandsBooleanEqualities)
{
  // (= (>= x 1) (>= y 1)) and (xor (>= x 1) (>= y 1)), which the negation
  // normal form keeps as connectives
  Node xAtLeastOne = nm->mkNode(Kind::GEQ, x, one);
  Node yAtLeastOne = nm->mkNode(Kind::GEQ, y, one);
  Node equality = xAtLeastOne.eqNode(yAtLeastOne);
  Node exclusiveOr = nm->mkNode(Kind::XOR, xAtLeastOne, yAtLeastOne);

  ASSERT_EQ("(or (and (>= x 1) (>= y 1)) (and (< x 1) (< y 1)))",
            LiaStarUtils::removeNot(equality, *e).toString());
  ASSERT_EQ("(or (and (>= x 1) (< y 1)) (and (< x 1) (>= y 1)))",
            LiaStarUtils::removeNot(exclusiveOr, *e).toString());
}

TEST_F(TestLiaStarUtils, toDNFExpandsBooleanEqualities)
{
  // (= (>= x 1) (<= x 2)) holds exactly for x in {1, 2}, so its DNF and the
  // DNF of its negation are combinations of constraints only
  Node atLeastOne = nm->mkNode(Kind::GEQ, x, one);
  Node atMostTwo = nm->mkNode(Kind::LEQ, x, two);
  Node equality = atLeastOne.eqNode(atMostTwo);
  Node negation = equality.notNode();
  Node vars = boundVarList({x});

  for (const Node& predicate : {equality, negation})
  {
    Node dnf = LiaStarUtils::toDNF(predicate, *e);
    ASSERT_TRUE(isEquivalent(predicate, dnf));
    ASSERT_NO_THROW(LiaStarUtils::getMatrices(vars, dnf));
  }
}

TEST_F(TestLiaStarUtils, removeItesGuardsWithTheConditionsOfBothSides)
{
  Node c1 = boolVar("c1"), c2 = boolVar("c2");
  // (>= (ite c1 x y) (ite c2 1 2)): each disjunct needs both conditions.
  // The ites are created in order, so (ite c1 x y) has the smaller id and
  // is split first, which fixes the order of the disjuncts.
  Node lhs = nm->mkNode(Kind::ITE, c1, x, y);
  Node rhs = nm->mkNode(Kind::ITE, c2, one, two);
  Node geq = nm->mkNode(Kind::GEQ, lhs, rhs);

  Node noItes = LiaStarUtils::removeItes(geq, *e);

  ASSERT_EQ(
      "(or (and (>= x 1) c1 c2) (and (>= x 2) c1 (not c2)) (and (>= y 1) "
      "(not c1) c2) (and (>= y 2) (not c1) (not c2)))",
      noItes.toString());
  ASSERT_TRUE(isEquivalent(geq, noItes));
}

TEST_F(TestLiaStarUtils, removeItesSplitsARepeatedIteOnce)
{
  Node c = boolVar("c");
  Node ite = nm->mkNode(Kind::ITE, c, x, y);
  // (>= (+ (ite c x y) (ite c x y)) 0): both occurrences take the same branch
  Node geq = nm->mkNode(Kind::GEQ, nm->mkNode(Kind::ADD, ite, ite), zero);

  Node noItes = LiaStarUtils::removeItes(geq, *e);

  ASSERT_EQ("(or (and (>= (* 2 x) 0) c) (and (>= (* 2 y) 0) (not c)))",
            noItes.toString());
  ASSERT_TRUE(isEquivalent(geq, noItes));
}

TEST_F(TestLiaStarUtils, removeItesKeepsAllOperands)
{
  Node c = boolVar("c");
  Node z = nm->mkBoundVar("z", intType);
  // (>= (+ (ite c x y) z x) 0): a sum with three operands
  Node sum = nm->mkNode(Kind::ADD, {nm->mkNode(Kind::ITE, c, x, y), z, x});
  Node geq = nm->mkNode(Kind::GEQ, sum, zero);

  Node noItes = LiaStarUtils::removeItes(geq, *e);

  ASSERT_FALSE(expr::hasSubtermKind(Kind::ITE, noItes)) << noItes;
  ASSERT_TRUE(isEquivalent(geq, noItes)) << noItes;
}

TEST_F(TestLiaStarUtils, removeItesExpandsBooleanItes)
{
  Node c = boolVar("c");
  // (ite c (>= x 1) (<= x 0))
  Node geq = nm->mkNode(Kind::GEQ, x, one);
  Node leq = nm->mkNode(Kind::LEQ, x, zero);
  Node ite = nm->mkNode(Kind::ITE, c, geq, leq);

  Node noItes = LiaStarUtils::removeItes(ite, *e);

  ASSERT_EQ("(or (and (>= x 1) c) (and (<= x 0) (not c)))", noItes.toString());
}

TEST_F(TestLiaStarUtils, removeItesInConditions)
{
  Node d = boolVar("d");
  // (>= (ite (>= (ite d x y) 0) x y) 1): the condition has an ite too
  Node condition = nm->mkNode(Kind::GEQ, nm->mkNode(Kind::ITE, d, x, y), zero);
  Node geq = nm->mkNode(Kind::GEQ, nm->mkNode(Kind::ITE, condition, x, y), one);

  Node noItes = LiaStarUtils::removeItes(geq, *e);

  ASSERT_FALSE(expr::hasSubtermKind(Kind::ITE, noItes)) << noItes;
  ASSERT_TRUE(isEquivalent(geq, noItes)) << noItes;
}

}  // namespace test
}  // namespace cvc5::internal

#endif /* CVC5_USE_NORMALIZ */
