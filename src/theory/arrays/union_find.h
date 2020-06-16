/*********************                                                        */
/*! \file union_find.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Path-compressing, backtrackable union-find using an undo
 ** stack. Refactored from the UF union-find.
 **
 ** Path-compressing, backtrackable union-find using an undo stack
 ** rather than storing items in a CDMap<>.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARRAYS__UNION_FIND_H
#define CVC4__THEORY__ARRAYS__UNION_FIND_H

#include <utility>
#include <vector>
#include <unordered_map>

#include "expr/node.h"
#include "context/cdo.h"

namespace CVC4 {

namespace context {
  class Context;
}/* CVC4::context namespace */

namespace theory {
namespace arrays {

// NodeType \in { Node, TNode }
template <class NodeType, class NodeHash>
class UnionFind : context::ContextNotifyObj {
  /** Our underlying map type. */
  typedef std::unordered_map<NodeType, NodeType, NodeHash> MapType;

  /**
   * Our map of Nodes to their canonical representatives.
   * If a Node is not present in the map, it is its own
   * representative.
   */
  MapType d_map;

  /** Our undo stack for changes made to d_map. */
  std::vector<std::pair<TNode, TNode> > d_trace;

  /** Our current offset in the d_trace stack (context-dependent). */
  context::CDO<size_t> d_offset;

 public:
  UnionFind(context::Context* ctxt) :
    context::ContextNotifyObj(ctxt),
    d_offset(ctxt, 0) {
  }

  /**
   * Return a Node's union-find representative, doing path compression.
   */
  inline TNode find(TNode n);

  /**
   * Return a Node's union-find representative, NOT doing path compression.
   * This is useful for Assert() statements, debug checking, and similar
   * things that you do NOT want to mutate the structure.
   */
  inline TNode debugFind(TNode n) const;

  /**
   * Set the canonical representative of n to newParent.  They should BOTH
   * be their own canonical representatives on entry to this funciton.
   */
  inline void setCanon(TNode n, TNode newParent);

  /**
   * Called by the Context when a pop occurs.  Cancels everything to the
   * current context level.  Overrides ContextNotifyObj::notify().
   */
  void notify();

};/* class UnionFind<> */

template <class NodeType, class NodeHash>
inline TNode UnionFind<NodeType, NodeHash>::debugFind(TNode n) const {
  typename MapType::const_iterator i = d_map.find(n);
  if(i == d_map.end()) {
    return n;
  } else {
    return debugFind((*i).second);
  }
}

template <class NodeType, class NodeHash>
inline TNode UnionFind<NodeType, NodeHash>::find(TNode n) {
  Trace("arraysuf") << "arraysUF find of " << n << std::endl;
  typename MapType::iterator i = d_map.find(n);
  if(i == d_map.end()) {
    Trace("arraysuf") << "arraysUF   it is rep" << std::endl;
    return n;
  } else {
    Trace("arraysuf") << "arraysUF   not rep: par is " << (*i).second << std::endl;
    std::pair<TNode, TNode> pr = *i;
    // our iterator is invalidated by the recursive call to find(),
    // since it mutates the map
    TNode p = find(pr.second);
    if(p == pr.second) {
      return p;
    }
    d_trace.push_back(std::make_pair(n, pr.second));
    d_offset = d_trace.size();
    Trace("arraysuf") << "arraysUF   setting canon of " << n << " : " << p << " @ " << d_trace.size() << std::endl;
    pr.second = p;
    d_map.insert(pr);
    return p;
  }
}

template <class NodeType, class NodeHash>
inline void UnionFind<NodeType, NodeHash>::setCanon(TNode n, TNode newParent) {
  Assert(d_map.find(n) == d_map.end());
  Assert(d_map.find(newParent) == d_map.end());
  if(n != newParent) {
    Trace("arraysuf") << "arraysUF setting canon of " << n << " : " << newParent << " @ " << d_trace.size() << std::endl;
    d_map[n] = newParent;
    d_trace.push_back(std::make_pair(n, TNode::null()));
    d_offset = d_trace.size();
  }
}

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /*CVC4__THEORY__ARRAYS__UNION_FIND_H */
