/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The file containing utilities used in solving optimization queries.
 */

#include "opt_util.h"

using namespace cvc5::omt;
using namespace cvc5;

OptimizationResult::OptimizationResult(Result r, TNode val)
    : d_result(r), d_value(val)
{
}
Node OptimizationResult::getOptimalValue() const { return d_value; }
Result OptimizationResult::getResult() const { return d_result; }
// currently we don't yet have infinity
bool OptimizationResult::isInfinity() const { return false; }
bool OptimizationResult::isNull() const { return d_result.isNull(); }
void OptimizationResult::set(Result r, TNode val)
{
  d_result = r;
  d_value = val;
}
void OptimizationResult::setOptimalValue(TNode val) { d_value = val; }
void OptimizationResult::setResult(Result r) { d_result = r; }

std::ostream& operator<<(std::ostream& out, const OptimizationResult& result)
{
  // check the output language first
  Language lang = options::ioutils::getOutputLang(out);
  if (!language::isLangSmt2(lang))
  {
    Unimplemented()
        << "Only the SMTLib2 language supports optimization right now";
  }
  out << "(" << result.getResult();
  switch (result.getResult().isSat())
  {
    case Result::SAT:
    case Result::SAT_UNKNOWN:
    {
      if (!result.isInfinity())
      {
        out << "\t" << result.getOptimalValue();
      }
      else
      {
        out << "\t" << result.getOptimalValue() << " * "
            << "Inf";
      }
      break;
    }
    case Result::UNSAT: break;
    default: Unreachable();
  }
  out << ")";
  return out;
}

Objective::Objective(TNode target, OptType type)
    : d_target(target), d_type(type), d_result()
{
  if (isBVUnsigned())
  {
    Assert(d_target.getType().isBitVector());
  }
}

bool Objective::isMaximize() const
{
  return d_type == OptType::MAXIMIZE || d_type == OptType::BV_MAXIMIZE_UNSIGNED;
}

bool Objective::isMinimize() const
{
  return d_type == OptType::MINIMIZE || d_type == OptType::BV_MINIMIZE_UNSIGNED;
}

bool Objective::isBVUnsigned() const
{
  return isBV()
         && (d_type == OptType::BV_MAXIMIZE_UNSIGNED
             || d_type == OptType::BV_MINIMIZE_UNSIGNED);
}

bool Objective::isBVSigned() const
{
  return isBV() && (d_type == OptType::MAXIMIZE || d_type == OptType::MINIMIZE);
}

bool Objective::isBV() const { return d_target.getType().isBitVector(); }

TNode Objective::getTarget() const { return d_target; }

OptType Objective::getType() const { return d_type; }

bool Objective::hasResult() const { return !(d_result.isNull()); }

OptimizationResult Objective::getOptResult() const { return d_result; }

void Objective::setOptResult(const OptimizationResult& res) const
{
  d_result = res;
}

std::ostream& operator<<(std::ostream& out, const Objective& objective)
{
  // check the output language first
  Language lang = options::ioutils::getOutputLang(out);
  if (!language::isLangSmt2(lang))
  {
    Unimplemented()
        << "Only the SMTLib2 language supports optimization right now";
  }
  out << "(";
  if (objective.isMinimize())
  {
    out << "minimize ";
  }
  else if (objective.isMaximize())
  {
    out << "maximize ";
  }
  TNode target = objective.getTarget();
  out << target;
  if (objective.isBV())
  {
    out << (objective.isBVSigned() ? " :signed" : " :unsigned");
  }
  out << ")";
  return out;
}
