/*********************                                                        */
/*! \file ite_removal.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Representation of cardinality
 **
 ** Simple class to represent a cardinality; used by the CVC4 type system
 ** give the cardinality of sorts.
 **/

#pragma once

#include <vector>
#include "expr/node.h"

namespace CVC4 {

class RemoveITE {

public:

  /**
   * Removes the ITE nodes by introducing skolem variables. All additional assertions are pushed into assertions.
   */
  static void run(std::vector<Node>& assertions);

  /**
   * Removes the ITE from the node by introducing skolem variables. All additional assertions are pushed into assertions.
   */
  static Node run(TNode node, std::vector<Node>& additionalAssertions);

};


}
