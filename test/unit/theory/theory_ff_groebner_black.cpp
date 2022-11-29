/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of ff incremental groebner basis computation.
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
#include "theory/ff/groebner.h"
#include "util/cocoa_globals.h"

namespace cvc5::internal {

using namespace kind;
using namespace context;
using namespace theory;

namespace test {

class TestTheoryFfGroebnerBlack : public TestSmt
{
  void SetUp() override
  {
    TestSmt::SetUp();
    initCocoaGlobalManager();
  }
};

TEST_F(TestTheoryFfGroebnerBlack, SingleVariable)
{
  CoCoA::ring ring = CoCoA::NewZZmod(7);
  std::vector<CoCoA::symbol> syms = CoCoA::symbols("a");
  CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
  ff::IncrementalIdeal ideal(d_slvEngine->getEnv(), polyRing);
  CoCoA::RingElem a = CoCoA::indet(polyRing, 0);
  ideal.pushGenerators({a * a - a});
  EXPECT_EQ(ideal.idealIsTrivial(), false);
  ideal.pushGenerators({a});
  EXPECT_EQ(ideal.idealIsTrivial(), false);
  EXPECT_EQ(ideal.hasSolution(), true);
  EXPECT_EQ(ideal.solution().front(), ring->myZero());
  ideal.pop();
  ideal.pushGenerators({a - 1});
  EXPECT_EQ(ideal.idealIsTrivial(), false);
  EXPECT_EQ(ideal.hasSolution(), true);
  EXPECT_EQ(ideal.solution().front(), ring->myOne());
  ideal.pop();
  ideal.pushGenerators({a - 2});
  EXPECT_EQ(ideal.idealIsTrivial(), true);
  EXPECT_EQ(ideal.hasSolution(), false);
  std::vector<CoCoA::RingElem> core{a * a - a, a - 2};
  EXPECT_EQ(ideal.trivialCore(), core);
  ideal.pop();
  ideal.pushGenerators({a * a - a});
  ideal.pushGenerators({a - 2});
  EXPECT_EQ(ideal.idealIsTrivial(), true);
  EXPECT_EQ(ideal.hasSolution(), false);
  core = {a * a - a, a - 2};
  EXPECT_EQ(ideal.trivialCore(), core);
}

TEST_F(TestTheoryFfGroebnerBlack, MultiVariable)
{
  CoCoA::ring ring = CoCoA::NewZZmod(7);
  std::vector<CoCoA::symbol> syms = CoCoA::symbols("a,b,c,d");
  CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
  ff::IncrementalIdeal ideal(d_slvEngine->getEnv(), polyRing);
  CoCoA::RingElem a = CoCoA::indet(polyRing, 0);
  CoCoA::RingElem b = CoCoA::indet(polyRing, 1);
  CoCoA::RingElem c = CoCoA::indet(polyRing, 2);
  CoCoA::RingElem d = CoCoA::indet(polyRing, 3);
  ideal.pushGenerators({a * a - a, b * b - b});
  EXPECT_EQ(ideal.idealIsTrivial(), false);
  ideal.pushGenerators({a - b});
  EXPECT_EQ(ideal.idealIsTrivial(), false);
  ideal.pushGenerators({c * c - c});
  EXPECT_EQ(ideal.idealIsTrivial(), false);
  ideal.pushGenerators({a - 1});
  EXPECT_EQ(ideal.idealIsTrivial(), false);
  ideal.pushGenerators({b - 1});
  EXPECT_EQ(ideal.idealIsTrivial(), false);
  ideal.pop();
  ideal.pushGenerators({b});
  EXPECT_EQ(ideal.idealIsTrivial(), true);
  std::vector<CoCoA::RingElem> core{a - b, a - 1, b};
  EXPECT_EQ(ideal.trivialCore(), core);
  ideal.pop();
  EXPECT_EQ(ideal.idealIsTrivial(), false);
  ideal.pushGenerators({c - 2});
  EXPECT_EQ(ideal.idealIsTrivial(), true);
  core = {c * c - c, c - 2};
  EXPECT_EQ(ideal.trivialCore(), core);
  ideal.pop();
  ideal.pop();
  ideal.pushGenerators({c - 2});
  EXPECT_EQ(ideal.idealIsTrivial(), true);
  core = {c * c - c, c - 2};
  EXPECT_EQ(ideal.trivialCore(), core);
  ideal.pop();
  ideal.pop();
  ideal.pop();
  ideal.pushGenerators({c * c - c});
  EXPECT_EQ(ideal.idealIsTrivial(), false);
  ideal.pushGenerators({c - 2});
  EXPECT_EQ(ideal.idealIsTrivial(), true);
  core = {c * c - c, c - 2};
  EXPECT_EQ(ideal.trivialCore(), core);
  ideal.pop();
  EXPECT_EQ(ideal.idealIsTrivial(), false);
  EXPECT_EQ(ideal.hasSolution(), true);
  EXPECT_TRUE(ideal.solution().front() == ring->myZero()
              || ideal.solution().front() == ring->myOne());
}

TEST_F(TestTheoryFfGroebnerBlack, MultiIdeals)
{
  CoCoA::ring ring1 = CoCoA::NewZZmod(7);
  CoCoA::ring ring2 = CoCoA::NewZZmod(11);
  std::vector<CoCoA::symbol> syms1 = CoCoA::symbols("a");
  std::vector<CoCoA::symbol> syms2 = CoCoA::symbols("b");
  CoCoA::PolyRing polyRing1 = CoCoA::NewPolyRing(ring1, syms1);
  CoCoA::PolyRing polyRing2 = CoCoA::NewPolyRing(ring2, syms2);
  ff::IncrementalIdeal ideal1(d_slvEngine->getEnv(), polyRing1);
  ff::IncrementalIdeal ideal2(d_slvEngine->getEnv(), polyRing2);
  CoCoA::RingElem a = CoCoA::indet(polyRing1, 0);
  CoCoA::RingElem b = CoCoA::indet(polyRing2, 0);

  ideal1.pushGenerators({a * a - a});
  EXPECT_EQ(ideal1.idealIsTrivial(), false);

  ideal2.pushGenerators({b * b - b});
  EXPECT_EQ(ideal1.idealIsTrivial(), false);

  ideal1.pushGenerators({a - 1});
  EXPECT_EQ(ideal1.idealIsTrivial(), false);
  EXPECT_EQ(ideal1.hasSolution(), true);
  EXPECT_EQ(ideal1.solution().front(), ring1->myOne());

  ideal2.pushGenerators({b - 2});
  EXPECT_EQ(ideal2.idealIsTrivial(), true);
  EXPECT_EQ(ideal2.hasSolution(), false);

  ideal1.pop();
  ideal1.pushGenerators({a - 5});
  EXPECT_EQ(ideal1.idealIsTrivial(), true);
  EXPECT_EQ(ideal1.hasSolution(), false);

  ideal2.pop();
  ideal2.pushGenerators({b});
  EXPECT_EQ(ideal2.idealIsTrivial(), false);
  EXPECT_EQ(ideal2.hasSolution(), true);
  EXPECT_EQ(ideal2.solution().front(), ring2->myZero());
}

TEST_F(TestTheoryFfGroebnerBlack, NoSolution)
{
  CoCoA::ring ring = CoCoA::NewZZmod(3);
  std::vector<CoCoA::symbol> syms = CoCoA::symbols("a,b");
  CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
  ff::IncrementalIdeal ideal(d_slvEngine->getEnv(), polyRing);
  CoCoA::RingElem a = CoCoA::indet(polyRing, 0);
  CoCoA::RingElem b = CoCoA::indet(polyRing, 1);

  ideal.pushGenerators({a * (a - 1) * (a - 2) - 1});
  EXPECT_EQ(ideal.idealIsTrivial(), false);
  EXPECT_EQ(ideal.hasSolution(), false);

  ideal.pop();

  ideal.pushGenerators({a * (a - 1) - b});
  EXPECT_EQ(ideal.idealIsTrivial(), false);
  EXPECT_EQ(ideal.hasSolution(), true);
  ideal.pushGenerators({b * (a - 2) - 1});
  EXPECT_EQ(ideal.idealIsTrivial(), false);
  EXPECT_EQ(ideal.hasSolution(), false);
}

}  // namespace test
}  // namespace cvc5::internal

#endif  // CVC5_USE_COCOA
