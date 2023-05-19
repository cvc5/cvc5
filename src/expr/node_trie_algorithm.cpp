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
 * Algorithms for node tries
 */

#include "expr/node_trie_algorithm.h"

namespace cvc5::internal {

void nodeTriePathPairProcess(const TNodeTrie* t,
                             size_t arity,
                             NodeTriePathPairProcessCallback& ntpc)
{
  std::vector<std::tuple<const TNodeTrie*, const TNodeTrie*, size_t>> visit;
  std::tuple<const TNodeTrie*, const TNodeTrie*, size_t> cur;
  const TNodeTrie* t1;
  const TNodeTrie* t2;
  size_t depth;
  visit.emplace_back(t, nullptr, 0);
  do
  {
    cur = visit.back();
    t1 = std::get<0>(cur);
    t2 = std::get<1>(cur);
    depth = std::get<2>(cur);
    visit.pop_back();
    if (depth == arity)
    {
      // We are at the leaves. If we split the path, process the data.
      if (t2 != nullptr)
      {
        ntpc.processData(t1->getData(), t2->getData());
      }
    }
    else if (t2 == nullptr)
    {
      // we are exploring paths with a common prefix
      if (depth < (arity - 1))
      {
        // continue exploring paths with common prefix, internal to each child
        for (const std::pair<const TNode, TNodeTrie>& tt : t1->d_data)
        {
          visit.emplace_back(&tt.second, nullptr, depth + 1);
        }
      }
      // consider splitting the path at this node
      for (std::map<TNode, TNodeTrie>::const_iterator it = t1->d_data.begin();
           it != t1->d_data.end();
           ++it)
      {
        std::map<TNode, TNodeTrie>::const_iterator it2 = it;
        ++it2;
        for (; it2 != t1->d_data.end(); ++it2)
        {
          if (ntpc.considerPath(it->first, it2->first))
          {
            visit.emplace_back(&it->second, &it2->second, depth + 1);
          }
        }
      }
    }
    else
    {
      Assert(t1 != t2);
      // considering two different paths, take the product of their children
      for (const std::pair<const TNode, TNodeTrie>& tt1 : t1->d_data)
      {
        for (const std::pair<const TNode, TNodeTrie>& tt2 : t2->d_data)
        {
          if (ntpc.considerPath(tt1.first, tt2.first))
          {
            visit.emplace_back(&tt1.second, &tt2.second, depth + 1);
          }
        }
      }
    }
  } while (!visit.empty());
}

}  // namespace cvc5::internal
