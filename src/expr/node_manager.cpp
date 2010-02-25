/*********************                                                        */
/** node_manager.cpp
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Expression manager implementation.
 **/

#include "node_manager.h"

using namespace std;
using namespace CVC4::expr;

namespace CVC4 {

__thread NodeManager* NodeManager::s_current = 0;

NodeValue* NodeManager::poolLookup(NodeValue* nv) const {
  NodeValueSet::const_iterator find = d_nodeValueSet.find(nv);
  if(find == d_nodeValueSet.end()) {
    return NULL;
  } else {
    return *find;
  }
}

}/* CVC4 namespace */
