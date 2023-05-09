/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of non-linear solver.
 */

#include "theory/arith/nl/strategy.h"

#include <iostream>

#include "base/check.h"
#include "options/arith_options.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

std::ostream& operator<<(std::ostream& os, InferStep step)
{
  switch (step)
  {
    case InferStep::BREAK: return os << "BREAK";
    case InferStep::FLUSH_WAITING_LEMMAS: return os << "FLUSH_WAITING_LEMMAS";
    case InferStep::COVERINGS_INIT: return os << "COVERINGS_INIT";
    case InferStep::COVERINGS_FULL: return os << "COVERINGS_FULL";
    case InferStep::NL_FACTORING: return os << "NL_FACTORING";
    case InferStep::IAND_INIT: return os << "IAND_INIT";
    case InferStep::IAND_FULL: return os << "IAND_FULL";
    case InferStep::IAND_INITIAL: return os << "IAND_INITIAL";
    case InferStep::POW2_INIT: return os << "POW2_INIT";
    case InferStep::POW2_FULL: return os << "POW2_FULL";
    case InferStep::POW2_INITIAL: return os << "POW2_INITIAL";
    case InferStep::ICP: return os << "ICP";
    case InferStep::NL_INIT: return os << "NL_INIT";
    case InferStep::NL_MONOMIAL_INFER_BOUNDS:
      return os << "NL_MONOMIAL_INFER_BOUNDS";
    case InferStep::NL_MONOMIAL_MAGNITUDE0:
      return os << "NL_MONOMIAL_MAGNITUDE0";
    case InferStep::NL_MONOMIAL_MAGNITUDE1:
      return os << "NL_MONOMIAL_MAGNITUDE1";
    case InferStep::NL_MONOMIAL_MAGNITUDE2:
      return os << "NL_MONOMIAL_MAGNITUDE2";
    case InferStep::NL_MONOMIAL_SIGN: return os << "NL_MONOMIAL_SIGN";
    case InferStep::NL_RESOLUTION_BOUNDS: return os << "NL_RESOLUTION_BOUNDS";
    case InferStep::NL_SPLIT_ZERO: return os << "NL_SPLIT_ZERO";
    case InferStep::NL_TANGENT_PLANES: return os << "NL_TANGENT_PLANES";
    case InferStep::NL_TANGENT_PLANES_WAITING:
      return os << "NL_TANGENT_PLANES_WAITING";
    case InferStep::TRANS_INIT: return os << "TRANS_INIT";
    case InferStep::TRANS_INITIAL: return os << "TRANS_INITIAL";
    case InferStep::TRANS_MONOTONIC: return os << "TRANS_MONOTONIC";
    case InferStep::TRANS_TANGENT_PLANES: return os << "TRANS_TANGENT_PLANES";
    default: Unreachable(); return os << "UNKNOWN_STEP";
  }
}

namespace {
/** Puts a new InferStep into a StepSequence */
inline StepSequence& operator<<(StepSequence& steps, InferStep s)
{
  steps.emplace_back(s);
  return steps;
}
}  // namespace

void Interleaving::add(const StepSequence& ss, std::size_t constant)
{
  d_branches.emplace_back(Branch{ss, constant});
  d_size += constant;
}
void Interleaving::resetCounter() { d_counter = 0; }

const StepSequence& Interleaving::get()
{
  Assert(!d_branches.empty())
      << "Can not get next sequence from an empty interleaving.";
  std::size_t cnt = d_counter;
  // Increase the counter
  d_counter = (d_counter + 1) % d_size;
  for (const auto& branch : d_branches)
  {
    if (cnt < branch.d_interleavingConstant)
    {
      // This is the current branch
      return branch.d_steps;
    }
    cnt -= branch.d_interleavingConstant;
  }
  Assert(false) << "Something went wrong.";
  return d_branches[0].d_steps;
}
bool Interleaving::empty() const { return d_branches.empty(); }

bool StepGenerator::hasNext() const { return d_next < d_steps.size(); }
InferStep StepGenerator::next() { return d_steps[d_next++]; }

bool Strategy::isStrategyInit() const { return !d_interleaving.empty(); }
void Strategy::initializeStrategy(const Options& options)
{
  StepSequence one;
  if (options.arith.nlICP)
  {
    one << InferStep::ICP << InferStep::BREAK;
  }
  if (options.arith.nlExt == options::NlExtMode::FULL
      || options.arith.nlExt == options::NlExtMode::LIGHT)
  {
    one << InferStep::NL_INIT << InferStep::BREAK;
  }
  if (options.arith.nlExt == options::NlExtMode::FULL)
  {
    one << InferStep::TRANS_INIT << InferStep::BREAK;
    if (options.arith.nlExtSplitZero)
    {
      one << InferStep::NL_SPLIT_ZERO << InferStep::BREAK;
    }
    one << InferStep::TRANS_INITIAL << InferStep::BREAK;
  }
  one << InferStep::IAND_INIT;
  one << InferStep::IAND_INITIAL << InferStep::BREAK;
  one << InferStep::POW2_INIT;
  one << InferStep::POW2_INITIAL << InferStep::BREAK;
  if (options.arith.nlExt == options::NlExtMode::FULL
      || options.arith.nlExt == options::NlExtMode::LIGHT)
  {
    one << InferStep::NL_MONOMIAL_SIGN << InferStep::BREAK;
    one << InferStep::NL_MONOMIAL_MAGNITUDE0 << InferStep::BREAK;
  }
  if (options.arith.nlExt == options::NlExtMode::FULL)
  {
    one << InferStep::TRANS_MONOTONIC << InferStep::BREAK;
    one << InferStep::NL_MONOMIAL_MAGNITUDE1 << InferStep::BREAK;
    one << InferStep::NL_MONOMIAL_MAGNITUDE2 << InferStep::BREAK;
    one << InferStep::NL_MONOMIAL_INFER_BOUNDS;
    if (options.arith.nlExtTangentPlanes
        && options.arith.nlExtTangentPlanesInterleave)
    {
      one << InferStep::NL_TANGENT_PLANES;
    }
    one << InferStep::BREAK;
    one << InferStep::FLUSH_WAITING_LEMMAS << InferStep::BREAK;
    if (options.arith.nlExtFactor)
    {
      one << InferStep::NL_FACTORING << InferStep::BREAK;
    }
    if (options.arith.nlExtResBound)
    {
      one << InferStep::NL_MONOMIAL_INFER_BOUNDS << InferStep::BREAK;
    }
    if (options.arith.nlExtTangentPlanes
        && !options.arith.nlExtTangentPlanesInterleave)
    {
      one << InferStep::NL_TANGENT_PLANES_WAITING;
    }
    if (options.arith.nlExtTfTangentPlanes)
    {
      one << InferStep::TRANS_TANGENT_PLANES;
    }
    one << InferStep::BREAK;
  }
  one << InferStep::IAND_FULL << InferStep::BREAK;
  one << InferStep::POW2_FULL << InferStep::BREAK;
  if (options.arith.nlCov)
  {
    one << InferStep::COVERINGS_INIT << InferStep::BREAK;
    one << InferStep::COVERINGS_FULL << InferStep::BREAK;
  }

  d_interleaving.add(one);
}
StepGenerator Strategy::getStrategy()
{
  return StepGenerator(d_interleaving.get());
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
