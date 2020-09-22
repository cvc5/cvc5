/*********************                                                        */
/*! \file node_self_iterator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Iterator supporting Node "self-iteration"
 **
 ** Iterator supporting Node "self-iteration."
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__NODE_SELF_ITERATOR_H
#define CVC4__EXPR__NODE_SELF_ITERATOR_H

#include <iterator>

#include "base/check.h"
#include "expr/node.h"

namespace CVC4 {
namespace expr {

class NodeSelfIterator : public std::iterator<std::input_iterator_tag, Node> {
  Node d_node;
  Node::const_iterator d_child;

public:
  static NodeSelfIterator self(TNode n);
  static NodeSelfIterator selfEnd(TNode n);

  NodeSelfIterator();
  NodeSelfIterator(Node n);
  NodeSelfIterator(TNode n);
  NodeSelfIterator(const NodeSelfIterator& i);

  NodeSelfIterator(Node::const_iterator i);
  NodeSelfIterator(TNode::const_iterator i);

  Node operator*() const;
  NodeSelfIterator& operator++();
  NodeSelfIterator operator++(int);

  bool operator==(NodeSelfIterator i) const;
  bool operator!=(NodeSelfIterator i) const;

};/* class NodeSelfIterator */

inline NodeSelfIterator NodeSelfIterator::self(TNode n) {
  Assert(!n.isNull()) << "Self-iteration over null nodes not permitted.";
  return NodeSelfIterator(n);
}

inline NodeSelfIterator NodeSelfIterator::selfEnd(TNode n) {
  Assert(!n.isNull()) << "Self-iteration over null nodes not permitted.";
  return NodeSelfIterator(n.end());
}

inline NodeSelfIterator::NodeSelfIterator() :
  d_node(),
  d_child() {
}

inline NodeSelfIterator::NodeSelfIterator(Node node) :
  d_node(node),
  d_child() {
  Assert(!node.isNull()) << "Self-iteration over null nodes not permitted.";
}

inline NodeSelfIterator::NodeSelfIterator(TNode node) :
  d_node(node),
  d_child() {
  Assert(!node.isNull()) << "Self-iteration over null nodes not permitted.";
}

inline NodeSelfIterator::NodeSelfIterator(const NodeSelfIterator& i) :
  d_node(i.d_node),
  d_child(i.d_child) {
}

inline NodeSelfIterator::NodeSelfIterator(Node::const_iterator i) :
  d_node(),
  d_child(i) {
}

inline NodeSelfIterator::NodeSelfIterator(TNode::const_iterator i) :
  d_node(),
  d_child(i) {
}

inline Node NodeSelfIterator::operator*() const {
  return d_node.isNull() ? *d_child : d_node;
}

inline NodeSelfIterator& NodeSelfIterator::operator++() {
  if(d_node.isNull()) {
    ++d_child;
  } else {
    d_child = d_node.end();
    d_node = Node::null();
  }
  return *this;
}

inline NodeSelfIterator NodeSelfIterator::operator++(int) {
  NodeSelfIterator i = *this;
  ++*this;
  return i;
}

inline bool NodeSelfIterator::operator==(NodeSelfIterator i) const {
  return d_node == i.d_node && d_child == i.d_child;
}

inline bool NodeSelfIterator::operator!=(NodeSelfIterator i) const {
  return !(*this == i);
}

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* CVC4__EXPR__NODE_SELF_ITERATOR_H */
