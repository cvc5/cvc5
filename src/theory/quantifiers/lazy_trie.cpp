/*********************                                                        */
/*! \file lazy_trie.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of lazy trie
 **/

#include "theory/quantifiers/lazy_trie.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

Node LazyTrie::add(Node n,
                   LazyTrieEvaluator* ev,
                   unsigned index,
                   unsigned ntotal,
                   bool forceKeep)
{
  LazyTrie* lt = this;
  while (lt != NULL)
  {
    if (index == ntotal)
    {
      // lazy child holds the leaf data
      if (lt->d_lazy_child.isNull() || forceKeep)
      {
        lt->d_lazy_child = n;
      }
      return lt->d_lazy_child;
    }
    if (lt->d_children.empty())
    {
      if (lt->d_lazy_child.isNull())
      {
        // no one has been here, we are done
        lt->d_lazy_child = n;
        return lt->d_lazy_child;
      }
      // evaluate the lazy child
      Node e_lc = ev->evaluate(lt->d_lazy_child, index);
      // store at next level
      lt->d_children[e_lc].d_lazy_child = lt->d_lazy_child;
      // replace
      lt->d_lazy_child = Node::null();
    }
    // recurse
    Node e = ev->evaluate(n, index);
    lt = &lt->d_children[e];
    index = index + 1;
  }
  return Node::null();
}

using IndTriePair = std::pair<unsigned, LazyTrie*>;

void DynamicClassifier::addClassifier(LazyTrieEvaluator* ev, unsigned ntotal)
{
  std::vector<IndTriePair> visit;
  unsigned index = 0;
  LazyTrie* trie;
  visit.push(IndTriePair(0, d_trie));
  while (!visit.empty())
  {
    index = visit.back().first;
    trie = &visit.back().second;
    visit.pop_back();
    // not at (previous) last level, traverse children
    if (index < ntotal)
    {
      for (const auto& p_nt : trie->d_children)
      {
        visit.push_back(IndTriePair(index + 1, &p_nt.second));
      }
      continue;
    }
    // last level, apply new classifier
    Node lc = trie->d_lazy_child;
    Assert(trie->d_children.empty() && !lc.isNull());
    std::vector<Node> prev_sep_class = d_rep_to_sepclass[lc];
    // make new sepclass of lc a singleton with itself
    d_rep_to_sepclass[lc].clear();
    d_rep_to_sepclass[lc].push_back(lc);
    // evaluate the lazy child and store at next level
    trie->d_children[ev->evaluate(lc, index + 1)].d_lazy_child = lc;
    // replace
    lc = Node::null();
    for (const Node& n : prev_sep_class)
    {
      Node eval = ev->evaluate(n, index + 1);
      if (trie->d_children[eval] != trie->d_children.end())
      {
        // add n to to map of item in next level
        d_rep_to_sepclass[trie->d_children[eval].d_lazy_child].push_back(n);
        continue;
      }
      // store at next level
      trie->d_children[eval].d_lazy_child = n;
      // create new map
      Assert(d_rep_to_sepclass[n] == d_rep_to_sepclass.end());
      d_rep_to_sepclass[n] = std::vector<Node>(n);
    }
  }
}

Node DynamicClassifier::add(Node f, LazyTrieEvaluator* ev, unsigned ntotal)
{
  Node res = d_trie.add(f, ev, 0, ntotal, false);
  // f was added to the separation class with representative res
  if (res != f)
  {
    Assert(d_rep_to_sepclass[res] != d_rep_to_sepclass.end());
    Assert(!d_rep_to_sepclass[res].empty());
    d_rep_to_sepclass[res].push_back(f);
    return;
  }
  // f is the representatitve of a singleton seperation class
  Assert(d_rep_to_sepclass[res] == d_rep_to_sepclass.end());
  d_rep_to_sepclass[res] = std::vector<Node>(f);
  return res;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
