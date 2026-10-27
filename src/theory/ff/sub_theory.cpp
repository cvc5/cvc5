/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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

#include <numeric>

#include "expr/node_traversal.h"
#include "options/ff_options.h"
#include "smt/env_obj.h"
#include "theory/ff/cocoa_encoder.h"
#include "theory/ff/core.h"
#include "theory/ff/gb.h"
#include "theory/ff/multi_roots.h"
#include "theory/ff/split_gb.h"
#include "theory/ff/util.h"
#include "util/cocoa_globals.h"
#include "util/finite_field_value.h"
#include "util/resource_manager.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

SubTheory::SubTheory(Env& env, FfStatistics* stats, const Integer& modulus)
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
  if (d_facts.empty()) return Result::SAT;
  if (e != Theory::EFFORT_FULL)
  {
    return {Result::UNKNOWN, UnknownExplanation::REQUIRES_FULL_CHECK, ""};
  }
  try
  {
    std::vector<Node> facts{};
    std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(facts));
    FfResult result;
    if (options().ff.ffSolver == options::FfSolver::SPLIT_GB)
    {
      result = split(facts, size(), d_env, d_stats);
    }
    else if (options().ff.ffSolver == options::FfSolver::GB)
    {
      result = gb(facts, size(), d_env, d_stats);
    }
    else
    {
      Unreachable() << options().ff.ffSolver << std::endl;
    }

    if (std::holds_alternative<FfModel>(result))
    {
      const auto nm = nodeManager();
      auto& model = std::get<FfModel>(result);
      Trace("ff::model") << "Model GF(" << size() << "):" << std::endl;
      for (const auto& [var, val] : model)
      {
        auto value = nm->mkConst<FiniteFieldValue>(val);
        Trace("ff::model") << " " << var << " = " << value << std::endl;
        d_model.insert({var, value});
      }
      return Result::SAT;
    }
    else if (std::holds_alternative<FfCore>(result))
    {
      d_conflict = std::get<FfCore>(result);
      return Result::UNSAT;
    }
    else
    {
      return {Result::UNKNOWN, UnknownExplanation::INCOMPLETE, ""};
    }
  }
  catch (FfTimeoutException& exc)
  {
    return {Result::UNKNOWN, UnknownExplanation::TIMEOUT, exc.getMessage()};
  }
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
