/*********************                                                        */
/*! \file union_find.cpp
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

#include <iostream>

#include "theory/uf/morgan/union_find.h"
#include "util/Assert.h"
#include "expr/node.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace uf {
namespace morgan {

template <class NodeType, class NodeHash>
void UnionFind<NodeType, NodeHash>::notify() {
  Trace("ufuf") << "UFUF cancelling : " << d_offset << " < " << d_trace.size() << " ?" << endl;
  while(d_offset < d_trace.size()) {
    pair<TNode, TNode> p = d_trace.back();
    if(p.second.isNull()) {
      d_map.erase(p.first);
      Trace("ufuf") << "UFUF   " << d_trace.size() << " erasing " << p.first << endl;
    } else {
      d_map[p.first] = p.second;
      Trace("ufuf") << "UFUF   " << d_trace.size() << " replacing " << p << endl;
    }
    d_trace.pop_back();
  }
  Trace("ufuf") << "UFUF cancelling finished." << endl;
}

// The following declarations allow us to put functions in the .cpp file
// instead of the header, since we know which instantiations are needed.

template void UnionFind<Node, NodeHashFunction>::notify();

template void UnionFind<TNode, TNodeHashFunction>::notify();

}/* CVC4::theory::uf::morgan namespace */
}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
