/*********************                                                        */
/*! \file stacking_map.h
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
 ** \brief Backtrackable map using an undo stack
 **
 ** Backtrackable map using an undo stack rather than storing items in
 ** a CDMap<>.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__UF__MORGAN__STACKING_MAP_H
#define __CVC4__THEORY__UF__MORGAN__STACKING_MAP_H

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
class StackingMap : context::ContextNotifyObj {
  /** Our underlying map type. */
  typedef __gnu_cxx::hash_map<NodeType, NodeType, NodeHash> MapType;

  /**
   * Our map of Nodes to their values.
   */
  MapType d_map;

  /** Our undo stack for changes made to d_map. */
  std::vector<std::pair<TNode, TNode> > d_trace;

  /** Our current offset in the d_trace stack (context-dependent). */
  context::CDO<size_t> d_offset;

public:
  StackingMap(context::Context* ctxt) :
    context::ContextNotifyObj(ctxt),
    d_offset(ctxt, 0) {
  }

  ~StackingMap() throw() { }

  /**
   * Return a Node's value in the key-value map.  If n is not a key in
   * the map, this function returns TNode::null().
   */
  TNode find(TNode n) const;

  /**
   * Set the value in the key-value map for Node n to newValue.
   */
  void set(TNode n, TNode newValue);

  /**
   * Called by the Context when a pop occurs.  Cancels everything to the
   * current context level.  Overrides ContextNotifyObj::notify().
   */
  void notify();

};/* class StackingMap<> */

}/* CVC4::theory::uf::morgan namespace */
}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /*__CVC4__THEORY__UF__MORGAN__STACKING_MAP_H */
