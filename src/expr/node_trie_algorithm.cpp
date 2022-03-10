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

void nodeTriePathCompareInternal(const TNodeTrie* t1,
                                 const TNodeTrie* t2,
                                 size_t arity,
                                 size_t depth,
                                 NodeTriePathCompareCallback& ntpc)
{
  if (depth == arity)
  {
    if (t2 != nullptr)
    {
      Node f1 = t1->getData();
      Node f2 = t2->getData();
      ntpc.processData(f1, f2);
    }
  }
  else if (t2 == nullptr)
  {
    if (depth < (arity - 1))
    {
      // add care pairs internal to each child
      for (const std::pair<const TNode, TNodeTrie>& tt : t1->d_data)
      {
        nodeTriePathCompareInternal(
            &tt.second, nullptr, arity, depth + 1, ntpc);
      }
    }
    // add care pairs based on each pair of non-disequal arguments
    for (std::map<TNode, TNodeTrie>::const_iterator it = t1->d_data.begin();
         it != t1->d_data.end();
         ++it)
    {
      std::map<TNode, TNodeTrie>::const_iterator it2 = it;
      ++it2;
      for (; it2 != t1->d_data.end(); ++it2)
      {
        if (ntpc.considerFork(it->first, it2->first))
        {
          nodeTriePathCompareInternal(
              &it->second, &it2->second, arity, depth + 1, ntpc);
        }
      }
    }
  }
  else
  {
    // add care pairs based on product of indices, non-disequal arguments
    for (const std::pair<const TNode, TNodeTrie>& tt1 : t1->d_data)
    {
      for (const std::pair<const TNode, TNodeTrie>& tt2 : t2->d_data)
      {
        if (ntpc.considerFork(tt1.first, tt2.first))
        {
          nodeTriePathCompareInternal(
              &tt1.second, &tt2.second, arity, depth + 1);
        }
      }
    }
  }
}

void nodeTriePathCompare(const TNodeTrie* t,
                         size_t n,
                         NodeTriePathCompareCallback& ntpc)
{
  nodeTriePathCompareInternal(t, nullptr, n, 0, ntpc);
}

}  // namespace cvc5
