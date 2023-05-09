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
 * Black box testing of ff univariate root finding.
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
#include "theory/ff/uni_roots.h"
#include "util/cocoa_globals.h"

namespace cvc5::internal {

using namespace kind;
using namespace context;
using namespace theory;

namespace test {

class TestTheoryFfRootsBlack : public TestSmt
{
  void SetUp() override
  {
    TestSmt::SetUp();
    initCocoaGlobalManager();
  }
};

#define TINY_MODULUS "7"
#define BIG_MODULUS                                                            \
  "57896044618658097711785492504343953926634992332820282019728792003956564819" \
  "949"

TEST_F(TestTheoryFfRootsBlack, DistinctRootsPoly)
{
  {
    CoCoA::BigInt p = CoCoA::BigIntFromString(TINY_MODULUS);
    CoCoA::ring ring = CoCoA::NewZZmod(p);
    std::vector<CoCoA::symbol> syms = CoCoA::symbols("x,y,z");
    CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
    CoCoA::RingElem x = CoCoA::indet(polyRing, 0);
    {
      CoCoA::RingElem f = x;
      CoCoA::RingElem ex = x;
      EXPECT_EQ(ff::distinctRootsPoly(f), ex);
    }

    {
      CoCoA::RingElem f = x * x * x;
      CoCoA::RingElem ex = x;
      EXPECT_EQ(ff::distinctRootsPoly(f), ex);
    }

    {
      CoCoA::RingElem f = x * x * x * (x - 1);
      CoCoA::RingElem ex = x * (x - 1);
      EXPECT_EQ(ff::distinctRootsPoly(f), ex);
    }

    {
      CoCoA::RingElem f = x * x * x * (x - 1) * (x * x + 1);
      CoCoA::RingElem ex = x * (x - 1);
      EXPECT_EQ(ff::distinctRootsPoly(f), ex);
    }
  }

  {
    // 2^255-19 (prime)
    CoCoA::BigInt p = CoCoA::BigIntFromString(BIG_MODULUS);
    CoCoA::ring ring = CoCoA::NewZZmod(p);
    std::vector<CoCoA::symbol> syms = CoCoA::symbols("x,y,z");
    CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
    CoCoA::RingElem x = CoCoA::indet(polyRing, 0);
    {
      CoCoA::RingElem f = x;
      CoCoA::RingElem ex = x;
      EXPECT_EQ(ff::distinctRootsPoly(f), ex);
    }

    {
      CoCoA::RingElem f = x * x * x;
      CoCoA::RingElem ex = x;
      EXPECT_EQ(ff::distinctRootsPoly(f), ex);
    }

    {
      CoCoA::RingElem f = x * x * x * (x - 1);
      CoCoA::RingElem ex = x * (x - 1);
      EXPECT_EQ(ff::distinctRootsPoly(f), ex);
    }

    {
      CoCoA::RingElem f = x * x * x * (x - 1) * (x * x + 2);
      CoCoA::RingElem ex = x * (x - 1);
      EXPECT_EQ(ff::distinctRootsPoly(f), ex);
    }
  }
}

TEST_F(TestTheoryFfRootsBlack, RootsZero)
{
  {
    CoCoA::BigInt p = CoCoA::BigIntFromString(TINY_MODULUS);
    CoCoA::ring ring = CoCoA::NewZZmod(p);
    std::vector<CoCoA::symbol> syms = CoCoA::symbols("x,y,z");
    CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
    CoCoA::RingElem x = CoCoA::indet(polyRing, 0);
    CoCoA::RingElem z = ring->myZero();
    {
      CoCoA::RingElem f = x;
      std::vector<CoCoA::RingElem> roots = {z + 0};
      EXPECT_EQ(ff::roots(f), roots);
    }

    {
      CoCoA::RingElem f = x * x * x;
      std::vector<CoCoA::RingElem> roots = {z + 0};
      EXPECT_EQ(ff::roots(f), roots);
    }

    {
      CoCoA::RingElem f = x * (x * x + 1);
      std::vector<CoCoA::RingElem> roots = {z + 0};
      EXPECT_EQ(ff::roots(f), roots);
    }
  }

  {
    CoCoA::BigInt p = CoCoA::BigIntFromString(BIG_MODULUS);
    CoCoA::ring ring = CoCoA::NewZZmod(p);
    std::vector<CoCoA::symbol> syms = CoCoA::symbols("x,y,z");
    CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
    CoCoA::RingElem x = CoCoA::indet(polyRing, 0);
    CoCoA::RingElem z = ring->myZero();
    {
      CoCoA::RingElem f = x;
      std::vector<CoCoA::RingElem> roots = {z + 0};
      EXPECT_EQ(ff::roots(f), roots);
    }

    {
      CoCoA::RingElem f = x * x * x;
      std::vector<CoCoA::RingElem> roots = {z + 0};
      EXPECT_EQ(ff::roots(f), roots);
    }

    {
      CoCoA::RingElem f = x * (x * x + 2);
      std::vector<CoCoA::RingElem> roots = {z + 0};
      EXPECT_EQ(ff::roots(f), roots);
    }
  }
}

TEST_F(TestTheoryFfRootsBlack, RootsFull)
{
  {
    CoCoA::BigInt p = CoCoA::BigIntFromString(TINY_MODULUS);
    CoCoA::ring ring = CoCoA::NewZZmod(p);
    std::vector<CoCoA::symbol> syms = CoCoA::symbols("x,y,z");
    CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
    CoCoA::RingElem x = CoCoA::indet(polyRing, 0);
    CoCoA::RingElem z = ring->myZero();

    {
      CoCoA::RingElem f = x * (x - 1);
      std::vector<CoCoA::RingElem> roots = {z + 0, z + 1};
      EXPECT_EQ(ff::roots(f), roots);
    }

    {
      CoCoA::RingElem f = x * (x - 1) * x * (x - 1);
      std::vector<CoCoA::RingElem> roots = {z + 0, z + 1};
      EXPECT_EQ(ff::roots(f), roots);
    }

    {
      CoCoA::RingElem f = x * (x - 1) * x * (x - 1) * (x * x + 1) * (x * x + 1);
      std::vector<CoCoA::RingElem> roots = {z + 0, z + 1};
      EXPECT_EQ(ff::roots(f), roots);
    }

    {
      CoCoA::RingElem f = (x * x + 1) * (x * x + 1);
      std::vector<CoCoA::RingElem> roots = {};
      EXPECT_EQ(ff::roots(f), roots);
    }

    {
      CoCoA::RingElem f = x * x - x + 1;
      std::vector<CoCoA::RingElem> roots = {z - 2, z + 3};
      EXPECT_EQ(ff::roots(f), roots);
    }
  }

  {
    CoCoA::BigInt p = CoCoA::BigIntFromString(BIG_MODULUS);
    CoCoA::ring ring = CoCoA::NewZZmod(p);
    std::vector<CoCoA::symbol> syms = CoCoA::symbols("x,y,z");
    CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
    CoCoA::RingElem x = CoCoA::indet(polyRing, 0);
    CoCoA::RingElem z = ring->myZero();

    {
      CoCoA::RingElem f = x * (x - 1);
      std::vector<CoCoA::RingElem> roots = {z + 0, z + 1};
      EXPECT_EQ(ff::roots(f), roots);
    }

    {
      CoCoA::RingElem f = x * (x - 1) * x * (x - 1);
      std::vector<CoCoA::RingElem> roots = {z + 0, z + 1};
      EXPECT_EQ(ff::roots(f), roots);
    }

    {
      CoCoA::RingElem f = x * (x - 1) * x * (x - 1) * (x * x + 2) * (x * x + 2);
      std::vector<CoCoA::RingElem> roots = {z + 0, z + 1};
      EXPECT_EQ(ff::roots(f), roots);
    }

    {
      CoCoA::RingElem f = (x * x + 2) * (x * x + 2);
      std::vector<CoCoA::RingElem> roots = {};
      EXPECT_EQ(ff::roots(f), roots);
    }

    {
      CoCoA::RingElem f = x * x - x + 1;
      std::vector<CoCoA::RingElem> roots = {
          CoCoA::RingElem(ring,
                          "-253802764370791375970922363645711810106321778329314"
                          "68165172742469126098314552"),
          CoCoA::RingElem(ring,
                          "2538027643707913759709223636457118101063217783293146"
                          "8165172742469126098314553"),
      };
      EXPECT_EQ(ff::roots(f), roots);
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
#endif  // CVC5_USE_COCOA
