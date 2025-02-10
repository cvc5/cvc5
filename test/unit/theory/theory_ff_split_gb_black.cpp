/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

#include "test_env.h"
#include "theory/ff/multi_roots.h"
#include "theory/ff/split_gb.h"
#include "util/cocoa_globals.h"
#include "util/random.h"
#include "util/resource_manager.h"

namespace cvc5::internal {

using namespace kind;
using namespace context;
using namespace theory;

namespace test {

class TestTheoryFfSplitGb : public TestEnv
{
  void SetUp() override
  {
    TestEnv::SetUp();
    initCocoaGlobalManager();
  }
};

CoCoA::RingElem randCoeff(const CoCoA::ring& polyRing, Random& rng)
{
  return CoCoA::zero(CoCoA::CoeffRing(polyRing)) + rng.rand();
}

CoCoA::RingElem randPoly(const CoCoA::ring& polyRing,
                         size_t degree,
                         size_t terms,
                         Random& rng)
{
  CoCoA::RingElem out = CoCoA::zero(polyRing);
  for (size_t ti = 0; ti < terms; ++ti)
  {
    CoCoA::RingElem term = CoCoA::zero(polyRing) + randCoeff(polyRing, rng);
    long tDegree = 1 + (rng.rand() % degree);
    for (long i = 0; i < tDegree; ++i)
    {
      long j = rng.rand() % CoCoA::NumIndets(polyRing);
      term *= CoCoA::indet(polyRing, j);
    }
    out += term;
  }
  return out;
}

CoCoA::RingElem randPolyWithRoot(const CoCoA::ring& polyRing,
                                 size_t degree,
                                 size_t terms,
                                 std::vector<CoCoA::RingElem> root,
                                 Random& rng)
{
  CoCoA::RingElem p = randPoly(polyRing, degree, terms, rng);
  CoCoA::RingElem val = ff::cocoaEval(p, root);
  return p - val;
}

TEST_F(TestTheoryFfSplitGb, RandSat)
{
  // two bases, random, always SAT
  size_t n_vars = 6;
  size_t degree = 2;
  size_t n_bases = 2;
  size_t n_terms = 2;
  size_t n_eqns = 1.5 * static_cast<double>(n_vars);
  size_t n_iters = 50;
  size_t modulus = 11;
  CoCoA::ring ring = CoCoA::NewZZmod(modulus);
  std::vector<CoCoA::symbol> syms = CoCoA::SymbolRange("x", 0, n_vars - 1);
  CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
  Random rng{0};
  for (size_t iter_i = 0; iter_i < n_iters; ++iter_i)
  {
    std::vector<CoCoA::RingElem> solution{};
    for (size_t i = 0; i < n_vars; ++i)
    {
      solution.push_back(randCoeff(polyRing, rng));
    }
    std::vector<std::vector<CoCoA::RingElem>> gens(n_bases);
    std::vector<CoCoA::RingElem> allGens;
    for (size_t i = 0; i < n_eqns; ++i)
    {
      allGens.push_back(
          randPolyWithRoot(polyRing, degree, n_terms, solution, rng));
      size_t j = rng.rand() % n_bases;
      gens[j].push_back(allGens.back());
    }
    std::vector<ff::Gb> bases;
    for (size_t i = 0; i < n_bases; ++i)
    {
      bases.emplace_back(gens[i], nullptr);
    }
    ff::BitProp nullBitProp{};
    bool isSat = ff::findZero(CoCoA::ideal(allGens), *d_env).size();
    ff::SplitGb splitBases(bases);
    auto result =
        ff::splitFindZero(std::move(splitBases), polyRing, nullBitProp, *d_env);
    ASSERT_EQ(result.has_value(), isSat);
    if (result.has_value())
    {
      ff::checkZero(bases, *result);
    }
  }
}

TEST_F(TestTheoryFfSplitGb, RandUnsat)
{
  size_t n_vars = 6;
  size_t degree = 2;
  size_t n_bases = 2;
  size_t n_terms = 1;
  size_t n_eqns = 1.5 * static_cast<double>(n_vars);
  size_t n_iters = 40;
  size_t modulus = 11;
  CoCoA::ring ring = CoCoA::NewZZmod(modulus);
  std::vector<CoCoA::symbol> syms = CoCoA::SymbolRange("x", 0, n_vars - 1);
  CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
  Random rng{0};
  for (size_t iter_i = 0; iter_i < n_iters; ++iter_i)
  {
    std::vector<std::vector<CoCoA::RingElem>> gens(n_bases);
    std::vector<CoCoA::RingElem> allGens;
    for (size_t i = 0; i < n_eqns; ++i)
    {
      allGens.push_back(randPoly(polyRing, degree, n_terms, rng));
      size_t j = rng.rand() % n_bases;
      gens[j].push_back(allGens.back());
    }
    std::vector<ff::Gb> bases;
    for (size_t i = 0; i < n_bases; ++i)
    {
      bases.emplace_back(gens[i], nullptr);
    }
    ff::BitProp nullBitProp{};
    bool isSat = ff::findZero(CoCoA::ideal(allGens), *d_env).size();
    ff::SplitGb splitBases(bases);
    auto result =
        ff::splitFindZero(std::move(splitBases), polyRing, nullBitProp, *d_env);
    ASSERT_EQ(result.has_value(), isSat);
    if (result.has_value())
    {
      ff::checkZero(bases, *result);
    }
  }
}

TEST_F(TestTheoryFfSplitGb, GbEmpty)
{
  size_t n_vars = 6;
  size_t modulus = 7;
  CoCoA::ring ring = CoCoA::NewZZmod(modulus);
  std::vector<CoCoA::symbol> syms = CoCoA::SymbolRange("x", 0, n_vars - 1);
  CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);

  // empty vector
  ff::Gb gb{std::vector<CoCoA::RingElem>(), nullptr};
  ASSERT_FALSE(gb.isWholeRing());
  ASSERT_FALSE(gb.zeroDimensional());
  ASSERT_EQ(gb.basis().size(), 0);
  for (size_t i = 0; i < n_vars; ++i)
  {
    ASSERT_FALSE(gb.contains(CoCoA::indet(polyRing, i)));
  }

  // no args
  ff::Gb gb2{};
  ASSERT_FALSE(gb2.isWholeRing());
  ASSERT_FALSE(gb2.zeroDimensional());
  ASSERT_EQ(gb2.basis().size(), 0);
  for (size_t i = 0; i < n_vars; ++i)
  {
    ASSERT_FALSE(gb2.contains(CoCoA::indet(polyRing, i)));
  }
}

TEST_F(TestTheoryFfSplitGb, GbRand)
{
  size_t n_vars = 6;
  size_t degree = 2;
  size_t n_terms = 2;
  size_t n_eqns = 4;
  size_t n_iters = 200;
  size_t modulus = 11;
  CoCoA::ring ring = CoCoA::NewZZmod(modulus);
  std::vector<CoCoA::symbol> syms = CoCoA::SymbolRange("x", 0, n_vars - 1);
  CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
  Random rng{0};
  for (size_t iter_i = 0; iter_i < n_iters; ++iter_i)
  {
    std::vector<CoCoA::RingElem> gens;
    for (size_t i = 0; i < n_eqns; ++i)
    {
      gens.push_back(randPoly(polyRing, degree, n_terms, rng));
    }
    CoCoA::ideal i(gens);
    ff::Gb gb(gens, nullptr);
    ASSERT_EQ(gb.isWholeRing(), CoCoA::IsZero(i));
    ASSERT_EQ(gb.zeroDimensional(), CoCoA::IsZeroDim(i));
    ASSERT_EQ(gb.basis().size(), CoCoA::GBasis(i).size());
    for (const auto& p : gb.basis())
    {
      ASSERT_TRUE(CoCoA::IsElem(p, i));
    }
    for (const auto& p : CoCoA::GBasis(i))
    {
      ASSERT_TRUE(gb.contains(p));
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
#endif  // CVC5_USE_COCOA
