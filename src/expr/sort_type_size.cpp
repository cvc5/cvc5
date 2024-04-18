/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sort type size utility. Used for model construction for higher-order.
 */

#include "expr/sort_type_size.h"

namespace cvc5::internal {

// compares the type size of i and j
// returns true iff the size of i is less than that of j
// tiebreaks are determined by node value
bool SortTypeSize::operator()(Node i, Node j)
{
  int si = getTypeSize(i.getType());
  int sj = getTypeSize(j.getType());
  if (si < sj)
  {
    return true;
  }
  else if (si == sj)
  {
    return i < j;
  }
  return false;
}
/** get the size of type tn */
size_t SortTypeSize::getTypeSize(const TypeNode& tn)
{
  std::map<TypeNode, size_t>::iterator it = d_type_size.find(tn);
  if (it != d_type_size.end())
  {
    return it->second;
  }
  size_t sum = 1;
  for (const TypeNode& tnc : tn)
  {
    sum += getTypeSize(tnc);
  }
  d_type_size[tn] = sum;
  return sum;
}

}  // namespace cvc5::internal
