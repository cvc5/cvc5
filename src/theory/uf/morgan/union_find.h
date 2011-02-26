/*********************                                                        */
/*! \file union_find.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Path-compressing, backtrackable union-find using an undo
 ** stack
 **
 ** Path-compressing, backtrackable union-find using an undo stack
 ** rather than storing items in a CDMap<>.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__UF__MORGAN__UNION_FIND_H
#define __CVC4__THEORY__UF__MORGAN__UNION_FIND_H

#include <utility>
#include <vector>
#include <ext/hash_map>

#include "expr/node.h"
#include "context/cdo.h"

namespace CVC4 {

namespace context {
  class Context;
}/* CVC4::context namespace */

namespace theory {
namespace uf {
namespace morgan {

// NodeType \in { Node, TNode }
template <class NodeType, class NodeHash>
class UnionFind : context::ContextNotifyObj {
  /** Our underlying map type. */
  typedef __gnu_cxx::hash_map<NodeType, NodeType, NodeHash> MapType;

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

  ~UnionFind() throw() { }

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
  Trace("ufuf") << "UFUF find of " << n << std::endl;
  typename MapType::iterator i = d_map.find(n);
  if(i == d_map.end()) {
    Trace("ufuf") << "UFUF   it is rep" << std::endl;
    return n;
  } else {
    Trace("ufuf") << "UFUF   not rep: par is " << (*i).second << std::endl;
    std::pair<TNode, TNode> pr = *i;
    // our iterator is invalidated by the recursive call to find(),
    // since it mutates the map
    TNode p = find(pr.second);
    if(p == pr.second) {
      return p;
    }
    d_trace.push_back(std::make_pair(n, pr.second));
    d_offset = d_trace.size();
    Trace("ufuf") << "UFUF   setting canon of " << n << " : " << p << " @ " << d_trace.size() << std::endl;
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
    Trace("ufuf") << "UFUF setting canon of " << n << " : " << newParent << " @ " << d_trace.size() << std::endl;
    d_map[n] = newParent;
    d_trace.push_back(std::make_pair(n, TNode::null()));
    d_offset = d_trace.size();
  }
}

}/* CVC4::theory::uf::morgan namespace */
}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /*__CVC4__THEORY__UF__MORGAN__UNION_FIND_H */
