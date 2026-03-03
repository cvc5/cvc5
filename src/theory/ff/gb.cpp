/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/gb.h"

// external includes
#include <CoCoA/ideal.H>
#include <CoCoA/ring.H>
#include <CoCoA/symbol.H>

// internal includes
#include "options/ff_options.h"
#include "theory/ff/cocoa_encoder.h"
#include "theory/ff/multi_roots.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

FfResult gb(const std::vector<Node>& facts,
            const FfSize& size,
            const Env& env,
            FfStatistics* stats)
{
  CocoaEncoder enc(env.getNodeManager(), size);
  // collect leaves
  for (const Node& node : facts)
  {
    enc.addFact(node);
  }
  enc.endScan();
  // assert facts
  for (const Node& node : facts)
  {
    enc.addFact(node);
  }

  // compute a GB
  std::vector<CoCoA::RingElem> generators;
  generators.insert(generators.end(), enc.polys().begin(), enc.polys().end());
  generators.insert(
      generators.end(), enc.bitsumPolys().begin(), enc.bitsumPolys().end());
  if (env.getOptions().ff.ffFieldPolys)
  {
    CoCoA::PolyRing polyRing(enc.polyRing());
    for (const auto& var : CoCoA::indets(polyRing))
    {
      CoCoA::BigInt characteristic = CoCoA::characteristic(enc.coeffRing());
      const long power = CoCoA::LogCardinality(enc.coeffRing());
      CoCoA::BigInt s = CoCoA::power(characteristic, power);
      generators.push_back(CoCoA::power(var, s) - var);
    }
  }
  Tracer tracer(generators);
  if (stats) ++stats->d_numGbRuns;
  if (env.getOptions().ff.ffTraceGb) tracer.setFunctionPointers();
  const CoCoA::ideal ideal = CoCoA::ideal(generators);
  std::vector<Poly> basis;
  {
    CodeTimer timer(stats ? &stats->d_timeGbRuns : nullptr);
    basis = GBasisTimeout(ideal, env.getResourceManager());
  }
  if (env.getOptions().ff.ffTraceGb) tracer.unsetFunctionPointers();

  // if it is trivial, create a conflict
  bool is_trivial = basis.size() == 1 && CoCoA::deg(basis.front()) == 0;
  if (is_trivial)
  {
    Trace("ff::gb") << "Trivial GB" << std::endl;
    if (stats) ++stats->d_numTrivialUnsat;
    if (env.getOptions().ff.ffTraceGb)
    {
      std::vector<size_t> coreIndices = tracer.trace(basis.front());
      FfCore conflict;
      for (size_t i = 0, n = facts.size(); i < n; ++i)
      {
        Trace("ff::core") << "In " << i << " : " << facts[i] << std::endl;
      }
      for (size_t i : coreIndices)
      {
        // omit (field polys, bitsum polys, ...) from core
        if (enc.polyHasFact(generators[i]))
        {
          Trace("ff::core") << "Core: " << i << " : " << facts[i] << std::endl;
          conflict.push_back(enc.polyFact(generators[i]));
        }
      }
      return conflict;
    }
    else
    {
      // set trivial conflict
      return facts;
    }
  }
  else
  {
    Trace("ff::gb") << "Non-trivial GB" << std::endl;

    // common root (vec of CoCoA base ring elements)

    std::vector<CoCoA::RingElem> root;
    {
      CodeTimer timer(stats ? &stats->d_modelConstructionTime : nullptr);
      root = findZero(ideal, env, stats);
    }

    if (root.empty())
    {
      // set trivial conflict
      return facts;
    }
    else
    {
      FfModel model;
      for (const auto& [idx, node] : enc.nodeIndets())
      {
        if (isFfLeaf(node))
        {
          model.emplace(node, enc.cocoaFfToFfVal(root[idx]));
        }
      }
      return model;
    }
  }
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif
