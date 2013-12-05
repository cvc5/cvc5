/*********************                                                        */
/*! \file first_order_reasoning.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Pre-process step for first-order reasoning
 **/

#include "cvc4_private.h"

#ifndef __CVC4__FIRST_ORDER_REASONING_H
#define __CVC4__FIRST_ORDER_REASONING_H

#include <iostream>
#include <string>
#include <vector>
#include <map>
#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {

class FirstOrderPropagation {
private:
  std::map< Node, Node > d_const_def;
  std::map< Node, bool > d_assertion_true;
  Node process(Node a, std::vector< Node > & lits);
  void collectLits( Node n, std::vector<Node> & lits );
  Node simplify( Node n );
public:
  FirstOrderPropagation(){}
  ~FirstOrderPropagation(){}

  void simplify( std::vector< Node >& assertions );
};

}

#endif
