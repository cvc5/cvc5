/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Multivariate root finding.
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/multi_roots.h"

#include <CoCoA/BigIntOps.H>
#include <CoCoA/RingFp.H>
#include <CoCoA/SparsePolyOps-MinPoly.H>
#include <CoCoA/SparsePolyOps-RingElem.H>
#include <CoCoA/SparsePolyOps-ideal.H>

#include <algorithm>
#include <memory>
#include <sstream>

#include "smt/assertions.h"
#include "theory/ff/uni_roots.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

AssignmentEnumerator::~AssignmentEnumerator(){};

ListEnumerator::ListEnumerator(const std::vector<CoCoA::RingElem>&& options)
    : d_remainingOptions(std::move(options))
{
  std::reverse(d_remainingOptions.begin(), d_remainingOptions.end());
}

ListEnumerator::~ListEnumerator(){};

std::optional<CoCoA::RingElem> ListEnumerator::next()
{
  if (d_remainingOptions.empty())
  {
    return {};
  }
  else
  {
    CoCoA::RingElem v = d_remainingOptions.back();
    d_remainingOptions.pop_back();
    return v;
  }
}

std::string ListEnumerator::name() { return "list"; }

std::unique_ptr<ListEnumerator> factorEnumerator(CoCoA::RingElem univariatePoly)
{
  int varIdx = CoCoA::UnivariateIndetIndex(univariatePoly);
  Assert(varIdx >= 0);
  Trace("ff::model::factor") << "roots for: " << univariatePoly << std::endl;
  std::vector<CoCoA::RingElem> theRoots = roots(univariatePoly);
  std::vector<CoCoA::RingElem> linears{};
  CoCoA::RingElem var = CoCoA::indet(CoCoA::owner(univariatePoly), varIdx);
  for (const auto& r : theRoots)
  {
    linears.push_back(var - r);
  }
  return std::make_unique<ListEnumerator>(std::move(linears));
}

RoundRobinEnumerator::RoundRobinEnumerator(
    const std::vector<CoCoA::RingElem>& vars, const CoCoA::ring& ring)
    : d_vars(vars),
      d_ring(ring),
      d_idx(),
      d_maxIdx(
          CoCoA::power(CoCoA::characteristic(ring), CoCoA::LogCardinality(ring))
          * vars.size())
{
}

RoundRobinEnumerator::~RoundRobinEnumerator() {}

std::optional<CoCoA::RingElem> RoundRobinEnumerator::next()
{
  std::optional<CoCoA::RingElem> ret{};
  if (d_idx != d_maxIdx)
  {
    size_t whichVar = d_idx % d_vars.size();
    CoCoA::BigInt whichVal = d_idx / d_vars.size();
    CoCoA::RingElem val = d_ring->myZero();
    val += whichVal;
    ret = d_vars[whichVar] - val;
    ++d_idx;
  }
  return ret;
}

std::string RoundRobinEnumerator::name() { return "round-robin"; }

bool isUnsat(const CoCoA::ideal& ideal)
{
  const auto& gens = CoCoA::GBasis(ideal);
  return !(gens.size() > 1 || CoCoA::deg(gens[0]) > 0);
}

template <typename T>
std::string ostring(const T& t)
{
  std::ostringstream o;
  o << t;
  return o.str();
}

std::pair<size_t, CoCoA::RingElem> extractAssignment(
    const CoCoA::RingElem& elem)
{
  Assert(CoCoA::deg(elem) == 1);
  Assert(CoCoA::NumTerms(elem) <= 2);
  CoCoA::RingElem m = CoCoA::monic(elem);
  int varNumber = CoCoA::UnivariateIndetIndex(elem);
  Assert(varNumber >= 0);
  return {varNumber, -CoCoA::ConstantCoeff(m)};
}

std::unordered_set<std::string> assignedVars(const CoCoA::ideal& ideal)
{
  std::unordered_set<std::string> ret{};
  for (const auto& g : CoCoA::GBasis(ideal))
  {
    if (CoCoA::deg(g) == 1)
    {
      int varNumber = CoCoA::UnivariateIndetIndex(g);
      if (varNumber >= 0)
      {
        ret.insert(ostring(CoCoA::indet(ideal->myRing(), varNumber)));
      }
    }
  }
  return ret;
}

bool allVarsAssigned(const CoCoA::ideal& ideal)
{
  return assignedVars(ideal).size()
         == (size_t)CoCoA::NumIndets(ideal->myRing());
}

std::unique_ptr<AssignmentEnumerator> brancher(const CoCoA::ideal& ideal)
{
  CoCoA::ring polyRing = ideal->myRing();
  Assert(!isUnsat(ideal));
  // first, we look for super-linear univariate polynomials.
  const auto& gens = CoCoA::GBasis(ideal);
  for (const auto& p : gens)
  {
    int varNumber = CoCoA::UnivariateIndetIndex(p);
    if (varNumber >= 0 && CoCoA::deg(p) > 1)
    {
      return factorEnumerator(p);
    }
  }
  // now, we check the dimension
  if (CoCoA::IsZeroDim(ideal))
  {
    // If zero-dimensional, we compute a minimal polynomial in some unset
    // variable.
    std::unordered_set<std::string> alreadySet = assignedVars(ideal);
    for (const auto& var : CoCoA::indets(polyRing))
    {
      std::string varName = ostring(var);
      if (!alreadySet.count(ostring(var)))
      {
        CoCoA::RingElem minPoly = CoCoA::MinPolyQuot(var, ideal, var);
        return factorEnumerator(minPoly);
      }
    }
    Unreachable()
        << "There should be no unset variables in zero-dimensional ideal";
  }
  else
  {
    // If positive dimensional, we make a list of unset variables and
    // round-robin guess.
    //
    // TODO(aozdemir): better model construction (cvc5-wishues/issues/138)
    std::unordered_set<std::string> alreadySet = assignedVars(ideal);
    std::vector<CoCoA::RingElem> toGuess{};
    for (const auto& var : CoCoA::indets(polyRing))
    {
      std::string varName = ostring(var);
      if (!alreadySet.count(ostring(var)))
      {
        toGuess.push_back(var);
      }
    }
    return std::make_unique<RoundRobinEnumerator>(toGuess,
                                                  polyRing->myBaseRing());
  }
}

std::vector<CoCoA::RingElem> commonRoot(const CoCoA::ideal& initialIdeal)
{
  CoCoA::ring polyRing = initialIdeal->myRing();
  // We maintain two stacks:
  // * one of ideals
  // * one of branchers
  //
  // If brancher B has the same index as ideal I, then B represents possible
  // expansions of ideal I (equivalently, restrictions of I's variety).
  std::vector<CoCoA::ideal> ideals{initialIdeal};
  if (TraceIsOn("ff::model::branch"))
  {
    Trace("ff::model::branch") << "init polys: " << std::endl;
    for (const auto& p : CoCoA::gens(initialIdeal))
    {
      Trace("ff::model::branch") << " * " << p << std::endl;
    }
  }
  std::vector<std::unique_ptr<AssignmentEnumerator>> branchers{};
  while (!ideals.empty())
  {
    const auto& ideal = ideals.back();
    // If the ideal is UNSAT, drop it.
    if (isUnsat(ideal))
    {
      ideals.pop_back();
    }
    // If the ideal has a linear polynomial in each variable, we've found a
    // variety element (a model).
    else if (allVarsAssigned(ideal))
    {
      std::unordered_map<size_t, CoCoA::RingElem> varNumToValue{};
      const auto& gens = CoCoA::GBasis(ideal);
      size_t numIndets = CoCoA::NumIndets(polyRing);
      Assert(gens.size() == numIndets);
      for (const auto& g : gens)
      {
        varNumToValue.insert(extractAssignment(g));
      }
      std::vector<CoCoA::RingElem> values{};
      for (size_t i = 0; i < numIndets; ++i)
      {
        values.push_back(varNumToValue[i]);
      }
      return values;
    }
    // If there are more ideals than branchers, branch
    else if (ideals.size() > branchers.size())
    {
      Assert(ideals.size() == branchers.size() + 1);
      branchers.push_back(brancher(ideal));
      Trace("ff::model::branch")
          << "brancher: " << branchers.back()->name() << std::endl;
      if (TraceIsOn("ff::model::branch"))
      {
        Trace("ff::model::branch") << "ideal polys: " << std::endl;
        for (const auto& p : CoCoA::gens(ideal))
        {
          Trace("ff::model::branch") << " * " << p << std::endl;
        }
      }
    }
    // Otherwise, this ideal should have a brancher; get the next branch
    else
    {
      Assert(ideals.size() == branchers.size());
      std::optional<CoCoA::RingElem> choicePoly = branchers.back()->next();
      // construct a new ideal from the branch
      if (choicePoly.has_value())
      {
        Trace("ff::model::branch")
            << "level: " << branchers.size()
            << ", brancher: " << branchers.back()->name()
            << ", branch: " << choicePoly.value() << std::endl;
        std::vector<CoCoA::RingElem> newGens = CoCoA::GBasis(ideal);
        newGens.push_back(choicePoly.value());
        ideals.push_back(CoCoA::ideal(newGens));
      }
      // or drop this ideal & brancher if we're out of branches.
      else
      {
        branchers.pop_back();
        ideals.pop_back();
      }
    }
  }
  // Could not find any solution; return empty.
  return {};
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
