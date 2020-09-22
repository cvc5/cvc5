/*********************                                                        */
/*! \file union_find.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Path-compressing, backtrackable union-find using an undo
 ** stack. Refactored from the UF union-find.
 **
 ** Path-compressing, backtrackable union-find using an undo stack
 ** rather than storing items in a CDMap<>.
 **/

#include <iostream>

#include "expr/node.h"
#include "theory/arrays/union_find.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arrays {

template <class NodeType, class NodeHash>
void UnionFind<NodeType, NodeHash>::notify() {
  Trace("arraysuf") << "arraysUF cancelling : " << d_offset << " < " << d_trace.size() << " ?" << endl;
  while(d_offset < d_trace.size()) {
    pair<TNode, TNode> p = d_trace.back();
    if(p.second.isNull()) {
      d_map.erase(p.first);
      Trace("arraysuf") << "arraysUF   " << d_trace.size() << " erasing " << p.first << endl;
    } else {
      d_map[p.first] = p.second;
      Trace("arraysuf") << "arraysUF   " << d_trace.size() << " replacing " << p << endl;
    }
    d_trace.pop_back();
  }
  Trace("arraysuf") << "arraysUF cancelling finished." << endl;
}

// The following declarations allow us to put functions in the .cpp file
// instead of the header, since we know which instantiations are needed.

template void UnionFind<Node, NodeHashFunction>::notify();

template void UnionFind<TNode, TNodeHashFunction>::notify();

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
