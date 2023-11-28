/******************************************************************************
 * Top contributors (to current version):
 *   Mikolas Janota, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of a trie that store subsets of tuples of term indices
 * that are not yielding  useful instantiations. of quantifier instantiation.
 * This is used in the term_tuple_enumerator.
 */
#include "theory/quantifiers/index_trie.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

void IndexTrie::add(const std::vector<bool>& mask,
                    const std::vector<Node>& values)
{
  const size_t cardinality = std::count(mask.begin(), mask.end(), true);
  if (d_ignoreFullySpecified && cardinality == mask.size())
  {
    return;
  }

  d_root = addRec(d_root, 0, cardinality, mask, values);
}

void IndexTrie::freeRec(IndexTrieNode* n)
{
  if (!n)
  {
    return;
  }
  for (auto c : n->d_children)
  {
    freeRec(c.second);
  }
  freeRec(n->d_blank);
  delete n;
}

bool IndexTrie::findRec(const IndexTrieNode* n,
                        size_t index,
                        const std::vector<Node>& members,
                        size_t& nonBlankLength) const
{
  if (!n || index >= members.size())
  {
    return true;  // all elements of members matched
  }
  if (n->d_blank && findRec(n->d_blank, index + 1, members, nonBlankLength))
  {
    return true;  // found in the blank branch
  }
  if (members[index].isNull())
  {
    // null is interpreted as "any", must have found in the blank branch
    return false;
  }
  nonBlankLength = index + 1;
  for (const auto& c : n->d_children)
  {
    if (c.first == members[index]
        && findRec(c.second, index + 1, members, nonBlankLength))
    {
      return true;  // found in the matching subtree
    }
  }
  return false;
}

IndexTrieNode* IndexTrie::addRec(IndexTrieNode* n,
                                 size_t index,
                                 size_t cardinality,
                                 const std::vector<bool>& mask,
                                 const std::vector<Node>& values)
{
  if (!n)
  {
    return nullptr;  // this tree matches everything, no point to add
  }
  if (cardinality == 0)  // all blanks, all strings match
  {
    freeRec(n);
    return nullptr;
  }

  Assert(index < mask.size());

  if (!mask[index])  // blank position in the added vector
  {
    auto blank = n->d_blank ? n->d_blank : new IndexTrieNode();
    n->d_blank = addRec(blank, index + 1, cardinality, mask, values);
    return n;
  }
  Assert(cardinality);
  Assert(!values[index].isNull());
  for (auto& edge : n->d_children)
  {
    if (edge.first == values[index])
    {
      // value already amongst the children
      edge.second =
          addRec(edge.second, index + 1, cardinality - 1, mask, values);
      return n;
    }
  }
  // new child needs to be added
  auto child =
      addRec(new IndexTrieNode(), index + 1, cardinality - 1, mask, values);
  n->d_children.push_back(std::make_pair(values[index], child));
  return n;
}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
