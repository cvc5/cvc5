/*********************                                                        */
/*! \file sygus_sampler.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
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
    std::vector<Node> ex;
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

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
