/*********************                                                        */
/*! \file ite_removal.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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

namespace CVC4 {

typedef std::hash_map<Node, unsigned, NodeHashFunction> IteSkolemMap;

class RemoveITE {

public:

  /**
   * Removes the ITE nodes by introducing skolem variables. All additional assertions are pushed into assertions.
   * iteSkolemMap contains a map from introduced skolem variables to the index in assertions containing the new
   * Boolean ite created in conjunction with that skolem variable.
   */
  static void run(std::vector<Node>& assertions, IteSkolemMap& iteSkolemMap);

  /**
   * Removes the ITE from the node by introducing skolem variables. All additional assertions are pushed into assertions.
   * iteSkolemMap contains a map from introduced skolem variables to the index in assertions containing the new
   * Boolean ite created in conjunction with that skolem variable.
   */
  static Node run(TNode node, std::vector<Node>& additionalAssertions,
                  IteSkolemMap& iteSkolemMap);

};/* class RemoveTTE */

}/* CVC4 namespace */
