/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of ff multivariate roots.
 */

#ifdef CVC5_USE_COCOA
#include <CoCoA/BigInt.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/RingZZ.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/SparsePolyRing.H>
#include <CoCoA/ring.H>
#include <CoCoA/symbol.H>

#include <memory>
#include <utility>

#include "test_smt.h"
#include "theory/ff/multi_roots.h"
#include "util/cocoa_globals.h"

namespace cvc5::internal {

using namespace kind;
using namespace context;
using namespace theory;

namespace test {

class TestTheoryFfModelBlack : public TestSmt
{
  void SetUp() override
  {
    TestSmt::SetUp();
    initCocoaGlobalManager();
  }
};

TEST_F(TestTheoryFfModelBlack, UnivariateEnumerator)
{
  CoCoA::ring ring = CoCoA::NewZZmod(7);
  {
    std::vector<CoCoA::symbol> syms = CoCoA::symbols("a");
    CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
    CoCoA::RingElem var = CoCoA::indet(polyRing, 0);
    std::vector<CoCoA::RingElem> assignments = {var - ring->myZero(),
                                                var - ring->myOne()};
    std::unique_ptr<ff::AssignmentEnumerator> a =
        std::make_unique<ff::ListEnumerator>(std::move(assignments));
    std::optional<CoCoA::RingElem> first = {var - ring->myZero()};
    std::optional<CoCoA::RingElem> second = {var - ring->myOne()};
    std::optional<CoCoA::RingElem> third = {};
    EXPECT_EQ(a->next(), first);
    EXPECT_EQ(a->next(), second);
    EXPECT_EQ(a->next(), third);
    EXPECT_EQ(a->next(), third);
    EXPECT_EQ(a->next(), third);
  }
}

TEST_F(TestTheoryFfModelBlack, RoundRobinEnumerator)
{
  CoCoA::ring ring = CoCoA::NewZZmod(3);
  {
    std::vector<CoCoA::symbol> syms = CoCoA::symbols("a,b,c");
    CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
    const std::vector<CoCoA::RingElem>& vars = CoCoA::indets(polyRing);
    std::vector<CoCoA::RingElem> vals{ring->myZero(), ring->myOne()};
    std::unique_ptr<ff::AssignmentEnumerator> a =
        std::make_unique<ff::RoundRobinEnumerator>(vars, ring);
    std::optional<CoCoA::RingElem> next{};
    CoCoA::RingElem zero = ring->myZero();
    CoCoA::RingElem one = ring->myZero() + 1;
    CoCoA::RingElem two = ring->myZero() + 2;
    next = vars[0] - zero;
    EXPECT_EQ(a->next(), next);
    next = vars[1] - zero;
    EXPECT_EQ(a->next(), next);
    next = vars[2] - zero;
    EXPECT_EQ(a->next(), next);
    next = vars[0] - one;
    EXPECT_EQ(a->next(), next);
    next = vars[1] - one;
    EXPECT_EQ(a->next(), next);
    next = vars[2] - one;
    EXPECT_EQ(a->next(), next);
    next = vars[0] - two;
    EXPECT_EQ(a->next(), next);
    next = vars[1] - two;
    EXPECT_EQ(a->next(), next);
    next = vars[2] - two;
    EXPECT_EQ(a->next(), next);
    next = {};
    EXPECT_EQ(a->next(), next);
    next = {};
    EXPECT_EQ(a->next(), next);
  }
}

TEST_F(TestTheoryFfModelBlack, IsUnsat)
{
  CoCoA::ring ring = CoCoA::NewZZmod(3);
  {
    std::vector<CoCoA::symbol> syms = CoCoA::symbols("a,b,c");
    CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
    CoCoA::RingElem a = CoCoA::indet(polyRing, 0);
    CoCoA::RingElem b = CoCoA::indet(polyRing, 1);
    CoCoA::RingElem c = CoCoA::indet(polyRing, 2);
    EXPECT_EQ(ff::isUnsat(CoCoA::ideal(a * (a - 1))), false);
    EXPECT_EQ(ff::isUnsat(CoCoA::ideal(a)), false);
    EXPECT_EQ(ff::isUnsat(CoCoA::ideal(a, b - 1)), false);
    EXPECT_EQ(ff::isUnsat(CoCoA::ideal(a, b - 1, c)), false);
    EXPECT_EQ(ff::isUnsat(CoCoA::ideal(a, a - 1)), true);
    // false b/c no field poly
    EXPECT_EQ(ff::isUnsat(CoCoA::ideal(a * (a - 1) * (a - 2) - 1)), false);
    EXPECT_EQ(
        ff::isUnsat(CoCoA::ideal(a * (a - 1) * (a - 2) - 1, a * a * a - a)),
        true);
    EXPECT_EQ(ff::isUnsat(CoCoA::ideal((a - b) * c - 1, a - b)), true);
  }
}

TEST_F(TestTheoryFfModelBlack, ExtractAssignment)
{
  CoCoA::ring ring = CoCoA::NewZZmod(3);
  {
    std::vector<CoCoA::symbol> syms = CoCoA::symbols("a,b,c");
    CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
    CoCoA::RingElem a = CoCoA::indet(polyRing, 0);
    CoCoA::RingElem c = CoCoA::indet(polyRing, 2);
    std::pair<size_t, CoCoA::RingElem> r;
    r = {0, ring->myOne()};
    EXPECT_EQ(ff::extractAssignment(a - 1), r);
    r = {0, ring->myZero()};
    EXPECT_EQ(ff::extractAssignment(a), r);
    r = {0, ring->myOne()};
    EXPECT_EQ(ff::extractAssignment((-a) + 1), r);
    r = {2, ring->myZero()};
    EXPECT_EQ(ff::extractAssignment(c), r);
  }
}

TEST_F(TestTheoryFfModelBlack, CommonRoot)
{
  CoCoA::ring ring = CoCoA::NewZZmod(3);
  std::vector<CoCoA::symbol> syms = CoCoA::symbols("a,b");
  CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
  CoCoA::RingElem a = CoCoA::indet(polyRing, 0);
  CoCoA::RingElem b = CoCoA::indet(polyRing, 1);
  CoCoA::RingElem z = ring->myZero();

  {
    std::vector<CoCoA::RingElem> gens = {a * a - a, b * b - b, a - b, a};
    std::vector<CoCoA::RingElem> values = {z, z};
    EXPECT_EQ(ff::commonRoot(CoCoA::ideal(gens)), values);
  }

  {
    std::vector<CoCoA::RingElem> gens = {a * a - a, b * b - b, a + b - 1, a};
    std::vector<CoCoA::RingElem> values = {z, z + 1};
    EXPECT_EQ(ff::commonRoot(CoCoA::ideal(gens)), values);
  }

  {
    std::vector<CoCoA::RingElem> gens = {a, a - 1};
    std::vector<CoCoA::RingElem> values = {};
    EXPECT_EQ(ff::commonRoot(CoCoA::ideal(gens)), values);
  }

  {
    std::vector<CoCoA::RingElem> gens = {a * (a - 1) * (a - 2) - 1};
    std::vector<CoCoA::RingElem> values = {};
    EXPECT_EQ(ff::commonRoot(CoCoA::ideal(gens)), values);
  }

  {
    std::vector<CoCoA::RingElem> gens = {a * b - 1};
    std::vector<CoCoA::RingElem> values = ff::commonRoot(CoCoA::ideal(gens));
    EXPECT_EQ(values[0] * values[1], z + 1);
  }

  {
    std::vector<CoCoA::RingElem> gens = {a * b - 1, b};
    std::vector<CoCoA::RingElem> values = ff::commonRoot(CoCoA::ideal(gens));
    EXPECT_EQ(values.size(), 0);
  }

  {
    std::vector<CoCoA::RingElem> gens = {a * b - 1, b - 2};
    std::vector<CoCoA::RingElem> values = {z + 2, z + 2};
    EXPECT_EQ(ff::commonRoot(CoCoA::ideal(gens)), values);
  }
}

TEST_F(TestTheoryFfModelBlack, CommonRootBig)
{
  CoCoA::ring ring = CoCoA::NewZZmod(17);
  std::vector<CoCoA::symbol> syms = CoCoA::symbols("a,b,c,d");
  CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
  CoCoA::RingElem a = CoCoA::indet(polyRing, 0);
  CoCoA::RingElem b = CoCoA::indet(polyRing, 1);
  CoCoA::RingElem c = CoCoA::indet(polyRing, 2);
  CoCoA::RingElem d = CoCoA::indet(polyRing, 3);
  CoCoA::RingElem z = ring->myZero();

  std::vector<CoCoA::RingElem> gens = {
      a * a - a, b * b - b, a - b, a, c * d - 1};
  std::vector<CoCoA::RingElem> values = ff::commonRoot(CoCoA::ideal(gens));
  EXPECT_EQ(values[0], z);
  EXPECT_EQ(values[1], z);
  EXPECT_EQ(values[2] * values[3], z + 1);
}

TEST_F(TestTheoryFfModelBlack, CommonRootCosntraints)
{
  CoCoA::ring ring = CoCoA::NewZZmod(17);
  std::vector<CoCoA::symbol> syms = CoCoA::symbols("a,b,c");
  CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
  CoCoA::RingElem a = CoCoA::indet(polyRing, 0);
  CoCoA::RingElem b = CoCoA::indet(polyRing, 1);
  CoCoA::RingElem c = CoCoA::indet(polyRing, 2);
  CoCoA::RingElem z = ring->myZero();
  // b is a perfect square
  // c is its inverse
  std::vector<CoCoA::RingElem> gens = {a * a - b, b * c - 1};
  std::vector<CoCoA::RingElem> values = ff::commonRoot(CoCoA::ideal(gens));
  EXPECT_EQ(values[0] * values[0], values[1]);
  EXPECT_EQ(values[1] * values[2], z + 1);
}

}  // namespace test
}  // namespace cvc5::internal
#endif  // CVC5_USE_COCOA
