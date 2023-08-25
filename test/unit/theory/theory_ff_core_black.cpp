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
 * Black box testing of groebner basis core computation.
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
#include "theory/ff/core.h"
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

TEST_F(TestTheoryFfRootsBlack, DistinctRootsPoly)
{
  {
    CoCoA::BigInt p = CoCoA::BigIntFromString(TINY_MODULUS);
    CoCoA::ring ring = CoCoA::NewZZmod(p);
    std::vector<CoCoA::symbol> syms = CoCoA::symbols("x,y,z");
    CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
    CoCoA::RingElem x = CoCoA::indet(polyRing, 0);
    CoCoA::RingElem y = CoCoA::indet(polyRing, 1);
    CoCoA::RingElem z = CoCoA::indet(polyRing, 2);
    std::vector<CoCoA::RingElem> gens{x,x-y,y-z,z*z-z,y-1,x-x*x};
    ff::Tracer tracer(gens);
    tracer.setFunctionPointers();
    CoCoA::ideal ideal(gens);
    std::vector<CoCoA::RingElem> basis = CoCoA::GBasis(ideal);
    ASSERT_EQ(basis.size(), 1);
    std::vector<size_t> idxs = tracer.trace(basis[0]);
    ASSERT_EQ(idxs.size(), 4);
    ASSERT_EQ(idxs[0], 0);
    ASSERT_EQ(idxs[1], 1);
    ASSERT_EQ(idxs[2], 2);
    ASSERT_EQ(idxs[3], 4);
  }
}

}  // namespace test
}  // namespace cvc5::internal
#endif  // CVC5_USE_COCOA
