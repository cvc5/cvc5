/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Algorithms for node tries
 */

#include "expr/node_trie_algorithm.h"

namespace cvc5 {

void nodeTriePathPairProcessInternal(const TNodeTrie* t1,
                                     const TNodeTrie* t2,
                                     size_t arity,
                                     size_t depth,
                                     NodeTriePathPairProcessCallback& ntpc)
{
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
        nodeTriePathPairProcessInternal(
            &tt.second, nullptr, arity, depth + 1, ntpc);
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
          nodeTriePathPairProcessInternal(
              &it->second, &it2->second, arity, depth + 1, ntpc);
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
          nodeTriePathPairProcessInternal(
              &tt1.second, &tt2.second, arity, depth + 1, ntpc);
        }
      }
    }
  }
}

void nodeTriePathPairProcess(const TNodeTrie* t,
                             size_t n,
                             NodeTriePathPairProcessCallback& ntpc)
{
  nodeTriePathPairProcessInternal(t, nullptr, n, 0, ntpc);
}

}  // namespace cvc5
