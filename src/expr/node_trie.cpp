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
TNode NodeTemplateTrie<ref_count>::existsTerm(std::vector<TNode>& reps) const
{
  const NodeTemplateTrie<ref_count>* tnt = this;
  std::map<TNode, NodeTemplateTrie<ref_count>>::const_iterator it;
  for (TNode r : reps)
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

template <bool ref_count>
bool NodeTemplateTrie<ref_count>::addTerm(TNode n, std::vector<TNode>& reps)
{
  return addOrGetTerm(n, reps) == n;
}

template <bool ref_count>
TNode NodeTemplateTrie<ref_count>::addOrGetTerm(TNode n, std::vector<TNode>& reps)
{
  NodeTemplateTrie<ref_count>* tnt = this;
  for (TNode r : reps)
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

template <bool ref_count>
void NodeTemplateTrie<ref_count>::debugPrint(const char* c, unsigned depth) const
{
  for (const std::pair<const TNode, NodeTemplateTrie<ref_count>>& p : d_data)
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
