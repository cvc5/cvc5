/*********************                                                        */
/*! \file union_find.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Path-compressing, backtrackable union-find using an undo
 ** stack. Refactored from the UF union-find.
 **
 ** Path-compressing, backtrackable union-find using an undo stack
 ** rather than storing items in a CDMap<>.
 **/

#include <iostream>

#include "theory/datatypes/union_find.h"
#include "util/Assert.h"
#include "expr/node.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace datatypes {

template <class NodeType, class NodeHash>
void UnionFind<NodeType, NodeHash>::contextNotifyPop() {
  Trace("datatypesuf") << "datatypesUF cancelling : " << d_offset << " < " << d_trace.size() << " ?" << endl;
  while(d_offset < d_trace.size()) {
    pair<TNode, TNode> p = d_trace.back();
    if(p.second.isNull()) {
      d_map.erase(p.first);
      Trace("datatypesuf") << "datatypesUF   " << d_trace.size() << " erasing " << p.first << endl;
    } else {
      d_map[p.first] = p.second;
      Trace("datatypesuf") << "datatypesUF   " << d_trace.size() << " replacing " << p << endl;
    }
    d_trace.pop_back();
  }
  Trace("datatypesuf") << "datatypesUF cancelling finished." << endl;
}

// The following declarations allow us to put functions in the .cpp file
// instead of the header, since we know which instantiations are needed.

template void UnionFind<Node, NodeHashFunction>::contextNotifyPop();

template void UnionFind<TNode, TNodeHashFunction>::contextNotifyPop();

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
