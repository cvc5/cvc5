/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 ** The classes in this file provide different views on a given node (e.g. an
 ** iterator that treats a certain kind as flattened).
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__NODE_VIEW_H
#define CVC5__EXPR__NODE_VIEW_H

#include <iterator>
#include <unordered_set>

#include "expr/node.h"
#include "expr/node_value.h"

namespace cvc5 {
namespace expr {

/**
 * This class provides an iterator over a node that treats a given kind as
 * flattened. There are two primary use cases for this class:
 *
 * - We can't always fully flatten operators because we may exceed the maximum
 *   number of children but we still want to treat a node as fully flattened.
 * - Materializing the flattened node is not required. In this case, this class
 *   provides a simple and efficient way to iterate over the node as if it were
 *   flattened.
 *
 * For example a node of the form (1 + 2) + (3 + 4) is treated as 1 + 2 + 3 + 4
 * by tihs class if we use "+" as the flattened kind.
 */
template <bool ref_count>
class FlatViewTemplate
{
 public:
  /**
   * Creates an instance of a flat view.
   *
   * @param node The node to iterate over. The node is expected to be of kind
   *             `kind`
   * @param kind The kind to treat as flattened
   * @param skipDups If true, then duplicate children are skipped
   */
  FlatViewTemplate(NodeTemplate<ref_count> node, bool skipDups = false);

  class iterator
  {
   public:
    using iterator_category = std::input_iterator_tag;
    using value_type = NodeTemplate<ref_count>;
    using difference_type = std::ptrdiff_t;
    using pointer = NodeTemplate<ref_count>*;
    using reference = NodeTemplate<ref_count>&;

    /**
     * Creates an instance of the iterator over a flat view.
     *
     * @param node The node to iterate over
     * @param end Determines whether this iterator should point to the end or
     *            the beginning
     * @param skipDups If true, then duplicate children are skipped
     */
    iterator(NodeTemplate<ref_count> node, bool end, bool skipDups);

    NodeTemplate<ref_count> operator*() const { return *d_iters.back().first; }

    bool operator==(const iterator& i) const
    {
      return d_iters.back().first == i.d_iters.back().first;
    }

    bool operator!=(const iterator& i) const
    {
      return d_iters.back().first != i.d_iters.back().first;
    }

    iterator& operator++();

    bool isDone()
    {
      return d_iters.size() == 1 && d_iters[0].first == d_iters[0].second;
    }

   private:
    /** The kind to be treated as flattened */
    Kind d_kind;
    /** Stack of iterators */
    std::vector<std::pair<NodeValue::iterator<NodeTemplate<ref_count>>,
                          NodeValue::iterator<NodeTemplate<ref_count>>>>
        d_iters;
    std::unordered_set<TNode> d_visited;
    /** True if the iterator should skip duplicates */
    bool d_skipDups;
  };

  /** Creates an iterator pointing to the first child */
  iterator begin() { return iterator(d_node, false, d_skipDups); }

  /** Creates an iterator pointing to the end */
  iterator end() { return iterator(d_node, true, d_skipDups); }

 private:
  /** The node to iterate over */
  NodeTemplate<ref_count> d_node;
  /** True if the iterator should skip duplicates */
  bool d_skipDups;
};

using FlatView = FlatViewTemplate<true>;
using FlatTView = FlatViewTemplate<false>;

}  // namespace expr
}  // namespace cvc5

#endif /* CVC5__EXPR__NODE_VIEW_H */
