/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for converting CaDiCaL-specific types to cvc5 types.
 */
#include "prop/cadical/util.h"

#include "base/check.h"

namespace cvc5::internal::prop::cadical {

SatValue toSatValue(int result)
{
  if (result == 10) return SAT_VALUE_TRUE;
  if (result == 20) return SAT_VALUE_FALSE;
  Assert(result == 0);
  return SAT_VALUE_UNKNOWN;
}

// Note: CaDiCaL returns lit/-lit for true/false. Older versions returned 1/-1.
SatValue toSatValueLit(int value)
{
  if (value > 0) return SAT_VALUE_TRUE;
  Assert(value < 0);
  return SAT_VALUE_FALSE;
}

CadicalLit toCadicalLit(const SatLiteral lit)
{
  return lit.isNegated() ? -lit.getSatVariable() : lit.getSatVariable();
}

SatLiteral toSatLiteral(CadicalLit lit)
{
  return SatLiteral(std::abs(lit), lit < 0);
}

CadicalVar toCadicalVar(SatVariable var) { return var; }

SatClause toSatClause(const std::unordered_set<int64_t>& activation_literals,
                      const std::vector<int32_t>& cl)
{
  SatClause clause;
  for (int32_t lit : cl)
  {
    // Filter out activation literals
    if (activation_literals.find(std::abs(lit)) == activation_literals.end())
    {
      clause.push_back(toSatLiteral(lit));
    }
  }
  return clause;
}

}  // namespace cvc5::internal::prop::cadical
