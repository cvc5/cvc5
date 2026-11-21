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
 * Ported from Z3: src/smt/watch_list.cpp.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 */

#include "theory/quantifiers/eager/watch_list.h"

#include <algorithm>

namespace cvc5::internal {
namespace theory::quantifiers::eager {

void WatchList::removeClause(Clause* c)
{
  auto it = std::find(d_clauses.begin(), d_clauses.end(), c);
  if (it != d_clauses.end())
  {
    d_clauses.erase(it);
  }
}

void WatchList::removeDeleted()
{
  d_clauses.erase(std::remove_if(d_clauses.begin(),
                                 d_clauses.end(),
                                 [](Clause* c) { return c->deleted(); }),
                  d_clauses.end());
}

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal
