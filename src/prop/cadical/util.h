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
#ifndef CVC5__PROP__CADICAL__UTIL_H
#define CVC5__PROP__CADICAL__UTIL_H

#include "base/check.h"
#include "prop/sat_solver_types.h"

namespace cvc5::internal::prop::cadical {

using CadicalLit = int;
using CadicalVar = int;

/**
 * Convert CaDiCaL result to SatValue.
 */
SatValue toSatValue(int result);

/**
 * Convert CaDiCaL value to SatValue.
 * Note: CaDiCaL returns lit/-lit for true/false. Older versions returned 1/-1.
 */
SatValue toSatValueLit(int value);

CadicalLit toCadicalLit(const SatLiteral lit);

/**
 * Convert SatLiteral to CaDiCaL literal.
 */
SatLiteral toSatLiteral(CadicalLit lit);

/**
 * Convert SatVariable to CaDiCaL variable.
 */
CadicalVar toCadicalVar(SatVariable var);

/**
 * Convert CaDiCaL clause to SatClause while filtering out activation literals.
 *
 * @param activation_literals Set of current activation literals.
 * @param cl CaDiCaL clause to convert.
 * @return The corresponding SatClause.
 */
SatClause toSatClause(const std::unordered_set<int64_t>& activation_literals,
                      const std::vector<int32_t>& cl);

}  // namespace cvc5::internal::prop::cadical

#endif
