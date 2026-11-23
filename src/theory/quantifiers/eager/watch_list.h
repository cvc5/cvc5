/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The watch list of a literal.
 *
 * Ported from Z3: src/smt/watch_list.h.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__WATCH_LIST_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__WATCH_LIST_H

#include <vector>

#include "prop/sat_solver_types.h"
#include "theory/quantifiers/eager/clause.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

/**
 * The list of clauses and literals watching a given literal.
 *
 * When used for unit propagation, a literal l1 in the watch list of l2
 * represents the binary clause (or l1 (not l2)).
 *
 * Z3 keeps both in one allocation, growing towards each other, so that the
 * literals are visited most recent first; getLiterals gives them in the order
 * they were inserted, and propagation visits them in reverse.
 */
class WatchList
{
 public:
  using ClauseIterator = Clause**;

  /** Remove all clauses and literals. */
  void reset()
  {
    d_clauses.clear();
    d_literals.clear();
  }

  /** An iterator to the first clause watching this literal. */
  ClauseIterator beginClause() { return d_clauses.data(); }

  /** The past-the-end iterator of the clauses watching this literal. */
  ClauseIterator endClause() { return d_clauses.data() + d_clauses.size(); }

  /** The binary watches, in the order they were inserted. */
  const std::vector<SatLiteral>& getLiterals() const { return d_literals; }

  /** Add c to the clauses watching this literal. */
  void insertClause(Clause* c) { d_clauses.push_back(c); }

  /** Add the binary watch l; see the class comment. */
  void insertLiteral(const SatLiteral& l) { d_literals.push_back(l); }

  /** Remove c from the clauses, if it is there. */
  void removeClause(Clause* c);

  /** Remove the clauses marked as deleted. */
  void removeDeleted();

  /** Drop the clauses from newEnd on, which must be in the list. */
  void setEndClause(ClauseIterator newEnd)
  {
    Assert(beginClause() <= newEnd && newEnd <= endClause());
    d_clauses.resize(static_cast<size_t>(newEnd - beginClause()));
  }

 private:
  /** The clauses watching this literal. */
  std::vector<Clause*> d_clauses;
  /** The binary watches, in the order they were inserted. */
  std::vector<SatLiteral> d_literals;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__WATCH_LIST_H */
