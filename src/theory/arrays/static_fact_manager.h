/*********************                                                        */
/*! \file static_fact_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Mathias Preiner, Morgan Deters
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

#ifndef CVC4__THEORY__ARRAYS__STATIC_FACT_MANAGER_H
#define CVC4__THEORY__ARRAYS__STATIC_FACT_MANAGER_H

#include <utility>
#include <vector>
#include <unordered_map>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace arrays {

  class StaticFactManager {
  /** Our underlying map type. */
  typedef std::unordered_map<Node, Node, NodeHashFunction> MapType;

  /**
   * Our map of Nodes to their canonical representatives.
   * If a Node is not present in the map, it is its own
   * representative.
   */
  MapType d_map;
  std::vector<Node> d_diseq;

public:
  StaticFactManager() {}

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

  bool areEq(TNode a, TNode b);
  bool areDiseq(TNode a, TNode b);
  void addDiseq(TNode eq);
  void addEq(TNode eq);

};/* class StaticFactManager<> */

inline TNode StaticFactManager::debugFind(TNode n) const {
  MapType::const_iterator i = d_map.find(n);
  if(i == d_map.end()) {
    return n;
  } else {
    return debugFind((*i).second);
  }
}

inline TNode StaticFactManager::find(TNode n) {
  Trace("arraysuf") << "arraysUF find of " << n << std::endl;
  MapType::iterator i = d_map.find(n);
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
    pr.second = p;
    d_map.insert(pr);
    return p;
  }
}

inline void StaticFactManager::setCanon(TNode n, TNode newParent) {
  Assert(d_map.find(n) == d_map.end());
  Assert(d_map.find(newParent) == d_map.end());
  if(n != newParent) {
    d_map[n] = newParent;
  }
}

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /*CVC4__THEORY__ARRAYS__STATIC_FACT_MANAGER_H */
