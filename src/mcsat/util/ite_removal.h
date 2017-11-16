/*********************                                                        */
/*! \file ite_removal.h
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Kshitij Bansal, Morgan Deters
 ** Minor contributors (to current version): Andrew Reynolds, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Removal of term ITEs
 **
 ** Removal of term ITEs.
 **/

#include "cvc4_private.h"

#pragma once

#include <vector>
#include "expr/node.h"
#include "util/dump.h"
#include "context/context.h"
#include "context/cdhashmap.h"

namespace CVC4 {

typedef std::hash_map<Node, unsigned, NodeHashFunction> IteSkolemMap;

class RemoveITE {
  typedef context::CDHashMap<Node, Node, NodeHashFunction> ITECache;
  ITECache d_iteCache;

public:

  RemoveITE(context::UserContext* u) :
    d_iteCache(u) {
  }

  /**
   * Removes the ITE nodes by introducing skolem variables. All
   * additional assertions are pushed into assertions. iteSkolemMap
   * contains a map from introduced skolem variables to the index in
   * assertions containing the new Boolean ite created in conjunction
   * with that skolem variable.
   */
  void run(std::vector<Node>& assertions, IteSkolemMap& iteSkolemMap);

  /**
   * Removes the ITE from the node by introducing skolem
   * variables. All additional assertions are pushed into
   * assertions. iteSkolemMap contains a map from introduced skolem
   * variables to the index in assertions containing the new Boolean
   * ite created in conjunction with that skolem variable.
   */
  Node run(TNode node, std::vector<Node>& additionalAssertions,
           IteSkolemMap& iteSkolemMap, std::vector<Node>& quantVar);

};/* class RemoveTTE */

}/* CVC4 namespace */
