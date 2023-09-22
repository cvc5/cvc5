/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Variadic trie utility
 */

#include "expr/variadic_trie.h"

namespace cvc5::internal {

bool VariadicTrie::add(Node n, const std::vector<Node>& i)
{
  VariadicTrie* curr = this;
  for (const Node& ic : i)
  {
    curr = &(curr->d_children[ic]);
  }
  if (curr->d_data.isNull())
  {
    curr->d_data = n;
    return true;
  }
  return false;
}

bool VariadicTrie::hasSubset(const std::vector<Node>& is) const
{
  if (!d_data.isNull())
  {
    return true;
  }
  for (const std::pair<const Node, VariadicTrie>& p : d_children)
  {
    Node n = p.first;
    if (std::find(is.begin(), is.end(), n) != is.end())
    {
      if (p.second.hasSubset(is))
      {
        return true;
      }
    }
  }
  return false;
}

}  // namespace cvc5::internal
