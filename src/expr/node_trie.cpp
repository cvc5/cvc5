/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of a trie class for Nodes and TNodes.
 */

#include "expr/node_trie.h"

namespace cvc5::internal {

template <bool ref_count>
NodeTemplate<ref_count> NodeTemplateTrie<ref_count>::existsTerm(
    const std::vector<NodeTemplate<ref_count>>& reps) const
{
  const NodeTemplateTrie<ref_count>* tnt = this;
  typename std::map<NodeTemplate<ref_count>,
                    NodeTemplateTrie<ref_count>>::const_iterator it;
  for (const NodeTemplate<ref_count>& r : reps)
  {
    it = tnt->d_data.find(r);
    if (it == tnt->d_data.end())
    {
      // didn't find this child, return null
      return Node::null();
    }
    tnt = &it->second;
  }
  if (tnt->d_data.empty())
  {
    return Node::null();
  }
  return tnt->d_data.begin()->first;
}

template TNode NodeTemplateTrie<false>::existsTerm(
    const std::vector<TNode>& reps) const;
template Node NodeTemplateTrie<true>::existsTerm(
    const std::vector<Node>& reps) const;

template <bool ref_count>
NodeTemplate<ref_count> NodeTemplateTrie<ref_count>::addOrGetTerm(
    NodeTemplate<ref_count> n, const std::vector<NodeTemplate<ref_count>>& reps)
{
  NodeTemplateTrie<ref_count>* tnt = this;
  for (const NodeTemplate<ref_count>& r : reps)
  {
    tnt = &(tnt->d_data[r]);
  }
  if (tnt->d_data.empty())
  {
    // Store n in d_data. This should be interpreted as the "data" and not as a
    // reference to a child.
    tnt->d_data[n].clear();
    return n;
  }
  return tnt->d_data.begin()->first;
}

template TNode NodeTemplateTrie<false>::addOrGetTerm(
    TNode n, const std::vector<TNode>& reps);
template Node NodeTemplateTrie<true>::addOrGetTerm(
    Node n, const std::vector<Node>& reps);

template <bool ref_count>
void NodeTemplateTrie<ref_count>::debugPrint(const char* c,
                                             unsigned depth) const
{
  for (const std::pair<const NodeTemplate<ref_count>,
                       NodeTemplateTrie<ref_count>>& p : d_data)
  {
    for (unsigned i = 0; i < depth; i++)
    {
      Trace(c) << "  ";
    }
    Trace(c) << p.first << std::endl;
    p.second.debugPrint(c, depth + 1);
  }
}

template void NodeTemplateTrie<false>::debugPrint(const char* c,
                                                  unsigned depth) const;
template void NodeTemplateTrie<true>::debugPrint(const char* c,
                                                 unsigned depth) const;


template <bool ref_count>
std::vector<Node> NodeTemplateTrie<ref_count>::getLeaves(size_t depth) const
{
  Assert(depth > 0);
  std::vector<Node> vec;
  std::vector<std::pair<const NodeTemplateTrie<ref_count>*, size_t>> visit;
  visit.emplace_back(this, depth);
  do
  {
    std::pair<const NodeTemplateTrie<ref_count>*, size_t> curr = visit.back();
    visit.pop_back();
    size_t currDepth = curr.second;
    for (const std::pair<const NodeTemplate<ref_count>,
                         NodeTemplateTrie<ref_count>>& p : curr.first->d_data)
    {
      if (currDepth == 0)
      {
        // we are at a leaf
        vec.push_back(p.first);
        break;
      }
      visit.emplace_back(&p.second, currDepth - 1);
    }
  } while (!visit.empty());
  return vec;
}

template std::vector<Node> NodeTemplateTrie<false>::getLeaves(
    size_t depth) const;
template std::vector<Node> NodeTemplateTrie<true>::getLeaves(
    size_t depth) const;

}  // namespace cvc5::internal
