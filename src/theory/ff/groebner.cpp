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
 * An incremental groebner basis engine.
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/groebner.h"

#include <CoCoA/BigInt.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/RingZZ.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/ring.H>

#include <numeric>

#include "expr/node_traversal.h"
#include "options/ff_options.h"
#include "theory/ff/model.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

IncrementalIdeal::IncrementalIdeal(Env& env, CoCoA::ring polyRing)
    : EnvObj(env),
      d_context(std::make_unique<context::Context>()),
      d_polyRing(polyRing),
      d_gens(d_context.get()),
      d_basis(d_context.get()),
      d_hasCore(d_context.get()),
      d_core(d_context.get()),
      d_hasSolution(d_context.get()),
      d_solution(d_context.get())
{
  if (options().ff.ffFieldPolys)
  {
    for (const auto& var : CoCoA::indets(polyRing))
    {
      CoCoA::BigInt characteristic =
          CoCoA::characteristic(polyRing->myBaseRing());
      long power = CoCoA::LogCardinality(polyRing->myBaseRing());
      CoCoA::BigInt size = CoCoA::power(characteristic, power);
      d_gens.push_back(CoCoA::power(var, size) - var);
      d_tracer.addInput(d_gens.back());
    }
    std::vector<CoCoA::RingElem> firstBasis;
    for (const auto& fieldPoly : d_gens)
    {
      firstBasis.push_back(fieldPoly);
    }
    d_basis = std::move(firstBasis);
  }
}

void IncrementalIdeal::pushGenerators(std::vector<CoCoA::RingElem>&& gens)
{
  d_context->push();
  d_tracer.push();
  std::vector<CoCoA::RingElem> theseGens = d_basis.get();
  for (auto& g : gens)
  {
    d_gens.emplace_back(std::move(g));
    d_tracer.addInput(d_gens.back());
    theseGens.push_back(d_gens.back());
  }
  d_tracer.setFunctionPointers();
  if (TraceIsOn("ff::groebner::push"))
  {
    for (const auto& b : theseGens)
    {
      Trace("ff::groebner::push") << "gens: " << b << std::endl;
    }
  }
  CoCoA::ideal ideal = CoCoA::ideal(theseGens);
  d_basis = CoCoA::GBasis(ideal);
  if (TraceIsOn("ff::groebner::push"))
  {
    for (const auto& b : d_basis.get())
    {
      Trace("ff::groebner::push") << "basis: " << b << std::endl;
    }
  }
  d_hasCore.set(false);
  d_hasSolution.set({});
}

bool IncrementalIdeal::idealIsTrivial()
{
  return d_basis.get().size() == 1 && CoCoA::deg(d_basis.get().front()) == 0;
}

const std::vector<size_t>& IncrementalIdeal::trivialCoreIndices()
{
  Assert(idealIsTrivial());
  if (!d_hasCore.get())
  {
    std::vector<size_t> indices;
    if (options().ff.ffTraceGb)
    {
      indices = d_tracer.trace(d_basis.get().front());
      if (options().ff.ffFieldPolys)
      {
        // we must shift out the field polynomial indices.
        std::vector<size_t> indicesWithoutFieldPolys;
        size_t numVars = CoCoA::NumIndets(d_polyRing);
        for (size_t i : indices)
        {
          if (i >= numVars)
          {
            indicesWithoutFieldPolys.push_back(i - numVars);
          }
        }
        indices = indicesWithoutFieldPolys;
      }
    }
    else
    {
      indices.clear();
      size_t numGens = d_gens.size();
      if (options().ff.ffFieldPolys)
      {
        numGens -= CoCoA::NumIndets(d_polyRing);
      }
      for (size_t i = 0; i < numGens; ++i)
      {
        indices.push_back(i);
      }
    }
    d_core = std::move(indices);
    d_hasCore.set(true);
  }
  return d_core.get();
}

std::vector<CoCoA::RingElem> IncrementalIdeal::trivialCore()
{
  std::vector<CoCoA::RingElem> r;
  for (size_t i : trivialCoreIndices())
  {
    r.push_back(d_gens[i]);
  }
  return r;
}

bool IncrementalIdeal::hasSolution()
{
  if (idealIsTrivial())
  {
    return false;
  }
  else
  {
    ensureSolution();
  }
  return d_hasSolution.get().value();
}

void IncrementalIdeal::ensureSolution()
{
  if (!d_hasSolution.get().has_value())
  {
    std::vector<CoCoA::RingElem> root = commonRoot(CoCoA::ideal(d_basis.get()));
    if (root.empty())
    {
      d_hasSolution.set({false});
    }
    else
    {
      d_hasSolution.set({true});
      d_solution.set(root);
    }
  }
}

const std::vector<CoCoA::RingElem>& IncrementalIdeal::solution()
{
  ensureSolution();
  return d_solution.get();
}

void IncrementalIdeal::pop()
{
  d_context->pop();
  d_tracer.pop();
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
