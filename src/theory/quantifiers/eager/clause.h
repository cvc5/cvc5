/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Clauses of the eager E-matching core.
 *
 * Ported from Z3: src/smt/smt_clause.h.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__CLAUSE_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__CLAUSE_H

#include <vector>

#include "base/check.h"
#include "prop/sat_solver_types.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

/** The Boolean variables and literals of the core are cvc5's SAT ones. */
using prop::SatLiteral;
using prop::SatVariable;

/** The variable reserved for the constant true. */
inline constexpr SatVariable s_trueBoolVar = 0;
/** The literal that is always true. */
inline constexpr SatLiteral s_trueLiteral(s_trueBoolVar, false);
/** The literal that is always false. */
inline constexpr SatLiteral s_falseLiteral(s_trueBoolVar, true);

/**
 * An auxiliary clause of the eager E-matching core, which encodes the Boolean
 * structure of the input and is deleted on backtracking. Its first two
 * literals are the watched ones.
 */
class Clause
{
 public:
  /** The clause of the numLits >= 2 literals lits, which are copied. */
  Clause(size_t numLits, const SatLiteral* lits)
      : d_lits(lits, lits + numLits), d_deleted(false)
  {
    Assert(numLits >= 2);
  }

  /** The idx-th literal. */
  SatLiteral getLiteral(size_t idx) const
  {
    Assert(idx < d_lits.size());
    return d_lits[idx];
  }

  /** Replace the idx-th literal by l, as when the watches change. */
  void setLiteral(size_t idx, SatLiteral l)
  {
    Assert(idx < d_lits.size());
    d_lits[idx] = l;
  }

  /** A pointer to the first literal. */
  SatLiteral* begin() { return d_lits.data(); }

  /** A pointer past the last literal. */
  SatLiteral* end() { return d_lits.data() + d_lits.size(); }

  /** Mark the clause for deletion; it must not be marked already. */
  void markAsDeleted()
  {
    Assert(!d_deleted);
    d_deleted = true;
  }

  /**
   * True if the clause is marked for deletion, by the batch deletion of
   * PropCore::notifyPopped, which then sweeps it from the watch lists.
   */
  bool deleted() const { return d_deleted; }

 private:
  /** The literals; the first two are watched. */
  std::vector<SatLiteral> d_lits;
  /** True if the clause is marked for deletion. */
  bool d_deleted;
};

using ClauseVector = std::vector<Clause*>;

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__CLAUSE_H */
