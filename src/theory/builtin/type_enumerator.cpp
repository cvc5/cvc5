/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Enumerator for uninterpreted sorts and functions.
 */

#include "theory/builtin/type_enumerator.h"

#include "theory/builtin/theory_builtin_rewriter.h"
#include "util/uninterpreted_sort_value.h"

namespace cvc5::internal {
namespace theory {
namespace builtin {

UninterpretedSortEnumerator::UninterpretedSortEnumerator(
    TypeNode type, TypeEnumeratorProperties* tep)
    : TypeEnumeratorBase<UninterpretedSortEnumerator>(type), d_count(0)
{
  Assert(type.isUninterpretedSort());
  d_has_fixed_bound = false;
  Trace("uf-type-enum") << "UF enum " << type << ", tep = " << tep << std::endl;
  if (tep && tep->d_fixed_usort_card)
  {
    d_has_fixed_bound = true;
    std::map<TypeNode, Integer>::iterator it = tep->d_fixed_card.find(type);
    if (it != tep->d_fixed_card.end())
    {
      d_fixed_bound = it->second;
    }
    else
    {
      d_fixed_bound = Integer(1);
    }
    Trace("uf-type-enum") << "...fixed bound : " << d_fixed_bound << std::endl;
  }
}

Node UninterpretedSortEnumerator::operator*()
{
  if (isFinished())
  {
    throw NoMoreValuesException(getType());
  }
  return NodeManager::currentNM()->mkConst(
      UninterpretedSortValue(getType(), d_count));
}

UninterpretedSortEnumerator& UninterpretedSortEnumerator::operator++()
{
  d_count += 1;
  return *this;
}

bool UninterpretedSortEnumerator::isFinished()
{
  if (d_has_fixed_bound)
  {
    return d_count >= d_fixed_bound;
  }
  return false;
}

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5::internal
