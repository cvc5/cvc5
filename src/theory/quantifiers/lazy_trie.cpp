/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of lazy trie.
 */

#include "theory/quantifiers/lazy_trie.h"

namespace cvc5::internal {
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

void LazyTrieMulti::addClassifier(LazyTrieEvaluator* ev, unsigned ntotal)
{
  Trace("lazy-trie-multi") << "LazyTrieM: Adding classifier " << ntotal + 1
                           << "\n";
  std::vector<IndTriePair> visit;
  unsigned index = 0;
  LazyTrie* trie;
  visit.push_back(IndTriePair(0, &d_trie));
  while (!visit.empty())
  {
    index = visit.back().first;
    trie = visit.back().second;
    visit.pop_back();
    // not at (previous) last level, traverse children
    if (index < ntotal)
    {
      for (std::pair<const Node, LazyTrie>& p_nt : trie->d_children)
      {
        visit.push_back(IndTriePair(index + 1, &p_nt.second));
      }
      continue;
    }
    Assert(trie->d_children.empty());
    // if last level and no element at leaf, ignore
    if (trie->d_lazy_child.isNull())
    {
      continue;
    }
    // apply new classifier
    Assert(d_rep_to_class.find(trie->d_lazy_child) != d_rep_to_class.end());
    std::vector<Node> prev_sep_class = d_rep_to_class[trie->d_lazy_child];
    if (TraceIsOn("lazy-trie-multi"))
    {
      Trace("lazy-trie-multi") << "...last level. Prev sep class: \n";
      for (const Node& n : prev_sep_class)
      {
        Trace("lazy-trie-multi") << "...... " << n << "\n";
      }
    }
    // make new sepclass of lc a singleton with itself
    d_rep_to_class.erase(trie->d_lazy_child);
    // replace
    trie->d_lazy_child = Node::null();
    for (const Node& n : prev_sep_class)
    {
      Node eval = ev->evaluate(n, index);
      std::map<Node, LazyTrie>::iterator it = trie->d_children.find(eval);
      if (it != trie->d_children.end())
      {
        // add n to to map of item in next level
        Trace("lazy-trie-multi") << "...add " << n << " to the class of "
                                 << it->second.d_lazy_child << "\n";
        d_rep_to_class[it->second.d_lazy_child].push_back(n);
        continue;
      }
      // store at next level
      trie->d_children[eval].d_lazy_child = n;
      // create new map
      Trace("lazy-trie-multi") << "...create new class for : " << n << "\n";
      Assert(d_rep_to_class.find(n) == d_rep_to_class.end());
      d_rep_to_class[n].clear();
      d_rep_to_class[n].push_back(n);
    }
  }
}

Node LazyTrieMulti::add(Node f, LazyTrieEvaluator* ev, unsigned ntotal)
{
  Trace("lazy-trie-multi") << "LazyTrieM: Adding " << f << "\n";
  Node res = d_trie.add(f, ev, 0, ntotal, false);
  // f was added to the separation class with representative res
  if (res != f)
  {
    Trace("lazy-trie-multi") << "... added " << f << " to the sepclass of "
                             << res << "\n";
    Assert(d_rep_to_class.find(res) != d_rep_to_class.end());
    Assert(!d_rep_to_class[res].empty());
    d_rep_to_class[res].push_back(f);
    return res;
  }
  // f is the representatitve of a singleton seperation class
  Trace("lazy-trie-multi") << "... added " << f
                           << " as the rep of the sepclass with itself\n";
  Assert(d_rep_to_class.find(res) == d_rep_to_class.end());
  d_rep_to_class[res].clear();
  d_rep_to_class[res].push_back(f);
  return res;
}

void LazyTrieMulti::clear()
{
  d_trie.clear();
  d_rep_to_class.clear();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
