/*********************                                                        */
/*! \file arithvar_node_map.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__ARITHVAR_NODE_MAP_H
#define CVC4__THEORY__ARITH__ARITHVAR_NODE_MAP_H


#include "theory/arith/arithvar.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdhashmap.h"
#include "context/cdo.h"

namespace CVC4 {
namespace theory {
namespace arith {

class ArithVarNodeMap {
private:
  /**
   * Bidirectional map between Nodes and ArithVars.
   */
  NodeToArithVarMap d_nodeToArithVarMap;
  ArithVarToNodeMap d_arithVarToNodeMap;

public:

  typedef ArithVarToNodeMap::const_iterator var_iterator;

  ArithVarNodeMap() {}

  inline bool hasArithVar(TNode x) const {
    return d_nodeToArithVarMap.find(x) != d_nodeToArithVarMap.end();
  }

  inline bool hasNode(ArithVar a) const {
    return d_arithVarToNodeMap.isKey(a);
  }

  inline ArithVar asArithVar(TNode x) const{
    Assert(hasArithVar(x));
    Assert((d_nodeToArithVarMap.find(x))->second <= ARITHVAR_SENTINEL);
    return (d_nodeToArithVarMap.find(x))->second;
  }

  inline Node asNode(ArithVar a) const{
    Assert(hasNode(a));
    return d_arithVarToNodeMap[a];
  }

  inline void setArithVar(TNode x, ArithVar a){
    Assert(!hasArithVar(x));
    Assert(!d_arithVarToNodeMap.isKey(a));
    d_arithVarToNodeMap.set(a, x);
    d_nodeToArithVarMap[x] = a;
  }

  inline void remove(ArithVar x){
    Assert(hasNode(x));
    Node node = asNode(x);

    d_nodeToArithVarMap.erase(d_nodeToArithVarMap.find(node));
    d_arithVarToNodeMap.remove(x);
  }

  var_iterator var_begin() const {
    return d_arithVarToNodeMap.begin();
  }
  var_iterator var_end() const {
    return d_arithVarToNodeMap.end();
  }

};/* class ArithVarNodeMap */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__ARITH__ARITHVAR_NODE_MAP_H */
