/*********************                                                        */
/*! \file node_trie.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of a trie class for Nodes and TNodes.
 **/

#include "expr/node_trie.h"

namespace CVC4 {
namespace theory {

template <bool ref_count>
NodeTemplate<ref_count> NodeTemplateTrie<ref_count>::existsTerm(const std::vector<NodeTemplate<ref_count>>& reps) const
{
  const NodeTemplateTrie<ref_count>* tnt = this;
  typename std::map<NodeTemplate<ref_count>, NodeTemplateTrie<ref_count>>::const_iterator it;
  for (const NodeTemplate<ref_count> r : reps)
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

template NodeTemplate<false> NodeTemplateTrie<false>::existsTerm(const std::vector<NodeTemplate<false>>& reps) const;
template NodeTemplate<true> NodeTemplateTrie<true>::existsTerm(const std::vector<NodeTemplate<true>>& reps) const;

template <bool ref_count>
NodeTemplate<ref_count> NodeTemplateTrie<ref_count>::addOrGetTerm(NodeTemplate<ref_count> n, const std::vector<NodeTemplate<ref_count>>& reps)
{
  NodeTemplateTrie<ref_count>* tnt = this;
  for (const NodeTemplate<ref_count> r : reps)
  {
    tnt = &(tnt->d_data[r]);
  }
  if (tnt->d_data.empty())
  {
    // Store n in d_data. This should be interpretted as the "data" and not as a
    // reference to a child.
    tnt->d_data[n].clear();
    return n;
  }
  return tnt->d_data.begin()->first;
}

template NodeTemplate<false> NodeTemplateTrie<false>::addOrGetTerm(NodeTemplate<false> n, const std::vector<NodeTemplate<false>>& reps);
template NodeTemplate<true> NodeTemplateTrie<true>::addOrGetTerm(NodeTemplate<true> n, const std::vector<NodeTemplate<true>>& reps);

template <bool ref_count>
void NodeTemplateTrie<ref_count>::debugPrint(const char* c, unsigned depth) const
{
  for (const std::pair<const NodeTemplate<ref_count>, NodeTemplateTrie<ref_count>>& p : d_data)
  {
    for (unsigned i = 0; i < depth; i++)
    {
      Trace(c) << "  ";
    }
    Trace(c) << p.first << std::endl;
    p.second.debugPrint(c, depth + 1);
  }
}

}  // namespace theory
}  // namespace CVC4
