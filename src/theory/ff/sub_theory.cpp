/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Daniel Larraz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A field-specific theory.
 * That is, the sub-theory for GF(p) for some fixed p.
 * Implements Figure 2, "DecisionProcedure" from [OKTB23].
 *
 * [OKTB23]: https://doi.org/10.1007/978-3-031-37703-7_8
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/sub_theory.h"

#include <CoCoA/BigInt.H>
#include <CoCoA/CpuTimeLimit.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/RingZZ.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/ring.H>

#include <numeric>

#include "expr/node_traversal.h"
#include "options/ff_options.h"
#include "smt/env_obj.h"
#include "theory/ff/cocoa_encoder.h"
#include "theory/ff/core.h"
#include "theory/ff/multi_roots.h"
#include "theory/ff/split_gb.h"
#include "theory/ff/util.h"
#include "util/cocoa_globals.h"
#include "util/finite_field_value.h"
#include "util/resource_manager.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

SubTheory::SubTheory(Env& env, FfStatistics* stats, Integer modulus)
    : EnvObj(env),
      FieldObj(nodeManager(), modulus),
      d_facts(context()),
      d_stats(stats)
{
  AlwaysAssert(modulus.isProbablePrime()) << "non-prime fields are unsupported";
  // must be initialized before using CoCoA.
  initCocoaGlobalManager();
}

void SubTheory::notifyFact(TNode fact) { d_facts.emplace_back(fact); }

Result SubTheory::postCheck(Theory::Effort e)
{
  d_conflict.clear();
  d_model.clear();
  // on some branches, we'll overwrite this result
  Result result = {
      Result::UNKNOWN, UnknownExplanation::UNKNOWN_REASON, "internal"};
  if (e == Theory::EFFORT_FULL)
  {
    try
    {
      if (d_facts.empty()) return Result::SAT;
      if (options().ff.ffSolver == options::FfSolver::SPLIT_GB)
      {
        std::vector<Node> facts{};
        std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(facts));
        const auto optModel = split(facts, size(), d_env);
        if (optModel.has_value())
        {
          const auto nm = nodeManager();
          for (const auto& [var, val] : optModel.value())
          {
            d_model.insert({var, nm->mkConst<FiniteFieldValue>(val)});
          }
          return Result::SAT;
        }
        std::copy(
            d_facts.begin(), d_facts.end(), std::back_inserter(d_conflict));
        return Result::UNSAT;
      }
      else if (options().ff.ffSolver == options::FfSolver::GB)
      {
        CocoaEncoder enc(nodeManager(), size());
        // collect leaves
        for (const Node& node : d_facts)
        {
          enc.addFact(node);
        }
        enc.endScan();
        // assert facts
        for (const Node& node : d_facts)
        {
          enc.addFact(node);
        }

        // compute a GB
        std::vector<CoCoA::RingElem> generators;
        generators.insert(
            generators.end(), enc.polys().begin(), enc.polys().end());
        generators.insert(generators.end(),
                          enc.bitsumPolys().begin(),
                          enc.bitsumPolys().end());
        if (options().ff.ffFieldPolys)
        {
          for (const auto& var : CoCoA::indets(enc.polyRing()))
          {
            CoCoA::BigInt characteristic = CoCoA::characteristic(coeffRing());
            const long power = CoCoA::LogCardinality(coeffRing());
            CoCoA::BigInt size = CoCoA::power(characteristic, power);
            generators.push_back(CoCoA::power(var, size) - var);
          }
        }
        Tracer tracer(generators);
        if (options().ff.ffTraceGb) tracer.setFunctionPointers();
        CoCoA::ideal ideal = CoCoA::ideal(generators);
        const auto basis = GBasisTimeout(ideal, d_env.getResourceManager());
        if (options().ff.ffTraceGb) tracer.unsetFunctionPointers();

        // if it is trivial, create a conflict
        bool is_trivial = basis.size() == 1 && CoCoA::deg(basis.front()) == 0;
        if (is_trivial)
        {
          Trace("ff::gb") << "Trivial GB" << std::endl;
          result = Result::UNSAT;
          if (options().ff.ffTraceGb)
          {
            std::vector<size_t> coreIndices = tracer.trace(basis.front());
            Assert(d_conflict.empty());
            for (size_t i = 0, n = d_facts.size(); i < n; ++i)
            {
              Trace("ff::core")
                  << "In " << i << " : " << d_facts[i] << std::endl;
            }
            for (size_t i : coreIndices)
            {
              // omit (field polys, bitsum polys, ...) from core
              if (enc.polyHasFact(generators[i]))
              {
                Trace("ff::core")
                    << "Core: " << i << " : " << d_facts[i] << std::endl;
                d_conflict.push_back(enc.polyFact(generators[i]));
              }
            }
          }
          else
          {
            setTrivialConflict();
          }
        }
        else
        {
          Trace("ff::gb") << "Non-trivial GB" << std::endl;

          // common root (vec of CoCoA base ring elements)
          std::vector<CoCoA::RingElem> root = findZero(ideal, d_env);

          if (root.empty())
          {
            result = Result::UNSAT;
            setTrivialConflict();
          }
          else
          {
            result = Result::SAT;
            // populate d_model from the root
            Assert(d_model.empty());
            const auto nm = nodeManager();
            Trace("ff::model") << "Model GF(" << size() << "):" << std::endl;
            for (const auto& [idx, node] : enc.nodeIndets())
            {
              if (isFfLeaf(node))
              {
                Node value = nm->mkConst(enc.cocoaFfToFfVal(root[idx]));
                Trace("ff::model")
                    << " " << node << " = " << value << std::endl;
                d_model.emplace(node, value);
              }
            }
          }
        }
      }
      else
      {
        Unreachable() << options().ff.ffSolver << std::endl;
      }
      AlwaysAssert(result.getStatus() != Result::UNKNOWN);
      return result;
    }
    catch (FfTimeoutException& exc)
    {
      return {Result::UNKNOWN, UnknownExplanation::TIMEOUT, exc.getMessage()};
    }
  }
  return {Result::UNKNOWN, UnknownExplanation::REQUIRES_FULL_CHECK, ""};
}

void SubTheory::setTrivialConflict()
{
  std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(d_conflict));
}

bool SubTheory::inConflict() const { return !d_conflict.empty(); }

const std::vector<Node>& SubTheory::conflict() const { return d_conflict; }

const std::unordered_map<Node, Node>& SubTheory::model() const
{
  return d_model;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
