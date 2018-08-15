/*********************                                                        */
/*! \file node_algorithm.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common algorithms on nodes
 **
 ** This file implements common algorithms applied to nodes, such as checking if
 ** a node contains a free or a bound variable. This file should generally only
 ** be included in source files.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__EXPR__NODE_ALGORITHM_H
#define __CVC4__EXPR__NODE_ALGORITHM_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace expr {

/**
 * A class that pretends iterating over a node of a certain kind. If the node
 * matches the kind, the class iterates over the children, otherwise the
 * iterator just points to the node. This is useful if you want to pretend to
 * iterate over a "unary" PLUS, for instance, since unary PLUSes don't exist.
 */
class KindedIterator
{
 public:
  KindedIterator(TNode n, Kind k) : d_node(n), d_kind(k) {}

  class iterator
  {
   public:
    TNode operator*() { return d_child < 0 ? d_node : d_node[d_child]; }

    bool operator==(const iterator& i)
    {
      return d_node == i.d_node && d_child == i.d_child;
    }

    bool operator!=(const iterator& i) { return !(*this == i); }

    iterator& operator++()
    {
      if (d_child != -1)
      {
        ++d_child;
      }
      return *this;
    }

    iterator operator++(int)
    {
      iterator i = *this;
      ++*this;
      return i;
    }

    static iterator begin(TNode n, Kind k)
    {
      return iterator(n, n.getKind() == k ? 0 : -2);
    }

    static iterator end(TNode n, Kind k)
    {
      return iterator(n, n.getKind() == k ? n.getNumChildren() : -1);
    }

   private:
    // The node this iterator iterates over
    TNode d_node;
    // The child that this iterator currenltly points to. If the node does not
    // match the kind, -1 indicates the end and -2 indicates the beginning.
    ssize_t d_child;

    iterator(TNode node, ssize_t child) : d_node(node), d_child(child) {}
  };

  /**
   * Returns an iterator that points to the beginning (either the first child of
   * the node if the node matches the kind or the node itself if it doesn't).
   */
  iterator begin() const { return iterator::begin(d_node, d_kind); }

  /**
   * Returns an iterator that points to the end (either past the last child of
   * the node if the node matches the kind or past the node itself if it
   * doesn't).
   */
  iterator end() const { return iterator::end(d_node, d_kind); }

 private:
  TNode d_node;
  Kind d_kind;
};

/**
 * Check if the node n has a subterm t.
 * @param n The node to search in
 * @param t The subterm to search for
 * @param strict If true, a term is not considered to be a subterm of itself
 * @return true iff t is a subterm in n
 */
bool hasSubterm(TNode n, TNode t, bool strict = false);

/**
 * Returns true iff the node n contains a bound variable. This bound
 * variable may or may not be free.
 * @param n The node under investigation
 * @return true iff this node contains a bound variable
 */
bool hasBoundVar(TNode n);

/**
 * Returns true iff the node n contains a free variable.
 * @param n The node under investigation
 * @return true iff this node contains a free variable.
 */
bool hasFreeVar(TNode n);

}  // namespace expr
}  // namespace CVC4

#endif
