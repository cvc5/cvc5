/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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
#include "expr/node.h"
#include "prop/sat_solver_types.h"

namespace cvc5::internal::prop {
class TheoryProxy;
}

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

/**
 * Convert a SatClause to its node representation.
 *
 * The literals are sorted by node id and duplicates are factored out, which
 * matches the normalization PropPfManager::normalizeAndRegister applies when
 * registering the proof of a clause. This is what makes the node returned here
 * the key under which the clause's proof can be looked up, both when the proof
 * tracer turns an original clause into an assumption of the SAT refutation and
 * when the propagator preserves the proof of a clause attached below the
 * current user level.
 *
 * @param nm The node manager.
 * @param proxy The theory proxy, used to map literals to nodes.
 * @param clause The clause to convert.
 * @return The corresponding clause node.
 */
Node toClauseNode(NodeManager* nm, TheoryProxy* proxy, const SatClause& clause);

}  // namespace cvc5::internal::prop::cadical

#endif
