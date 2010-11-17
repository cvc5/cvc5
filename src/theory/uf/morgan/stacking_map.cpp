/*********************                                                        */
/*! \file stacking_map.cpp
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

#include <iostream>

#include "theory/uf/morgan/stacking_map.h"
#include "util/Assert.h"
#include "expr/node.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace uf {
namespace morgan {

template <class NodeType, class NodeHash>
TNode StackingMap<NodeType, NodeHash>::find(TNode n) const {
  typename MapType::const_iterator i = d_map.find(n);
  if(i == d_map.end()) {
    return TNode();
  } else {
    return (*i).second;
  }
}

template <class NodeType, class NodeHash>
void StackingMap<NodeType, NodeHash>::set(TNode n, TNode newValue) {
  Trace("ufsm") << "UFSM setting " << n << " : " << newValue << " @ " << d_trace.size() << endl;
  NodeType& ref = d_map[n];
  d_trace.push_back(make_pair(n, TNode(ref)));
  d_offset = d_trace.size();
  ref = newValue;
}

template <class NodeType, class NodeHash>
void StackingMap<NodeType, NodeHash>::notify() {
  Trace("ufsm") << "UFSM cancelling : " << d_offset << " < " << d_trace.size() << " ?" << endl;
  while(d_offset < d_trace.size()) {
    pair<TNode, TNode> p = d_trace.back();
    if(p.second.isNull()) {
      d_map.erase(p.first);
      Trace("ufsm") << "UFSM   " << d_trace.size() << " erasing " << p.first << endl;
    } else {
      d_map[p.first] = p.second;
      Trace("ufsm") << "UFSM   " << d_trace.size() << " replacing " << p << endl;
    }
    d_trace.pop_back();
  }
  Trace("ufufsm") << "UFSM cancelling finished." << endl;
}

// The following declarations allow us to put functions in the .cpp file
// instead of the header, since we know which instantiations are needed.

template TNode StackingMap<Node, NodeHashFunction>::find(TNode n) const;
template void StackingMap<Node, NodeHashFunction>::set(TNode n, TNode newValue);
template void StackingMap<Node, NodeHashFunction>::notify();

template TNode StackingMap<TNode, TNodeHashFunction>::find(TNode n) const;
template void StackingMap<TNode, TNodeHashFunction>::set(TNode n, TNode newValue);
template void StackingMap<TNode, TNodeHashFunction>::notify();

}/* CVC4::theory::uf::morgan namespace */
}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
