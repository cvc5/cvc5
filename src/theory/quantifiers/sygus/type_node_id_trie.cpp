/*********************                                                        */
/*! \file type_node_id_trie.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of type node identifier trie
 **/

#include "theory/quantifiers/sygus/type_node_id_trie.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void TypeNodeIdTrie::add(Node v, std::vector<TypeNode>& types)
{
  TypeNodeIdTrie* tnt = this;
  for (unsigned i = 0, size = types.size(); i < size; i++)
  {
    tnt = &tnt->d_children[types[i]];
  }
  tnt->d_data.push_back(v);
}

void TypeNodeIdTrie::assignIds(std::map<Node, unsigned>& assign,
                               unsigned& idCount)
{
  if (!d_data.empty())
  {
    for (const Node& v : d_data)
    {
      assign[v] = idCount;
    }
    idCount++;
  }
  for (std::pair<const TypeNode, TypeNodeIdTrie>& c : d_children)
  {
    c.second.assignIds(assign, idCount);
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
