/*********************                                                        */
/*! \file boolean_simplification.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Simple routines for Boolean simplification
 **
 ** Simple, commonly-used routines for Boolean simplification.
 **/

#include "util/boolean_simplification.h"

namespace CVC4 {

void
BooleanSimplification::push_back_associative_commute_recursive
    (Node n, std::vector<Node>& buffer, Kind k, Kind notK, bool negateNode)
    throw(AssertionException) {
  Node::iterator i = n.begin(), end = n.end();
  for(; i != end; ++i){
    Node child = *i;
    if(child.getKind() == k){
      push_back_associative_commute_recursive(child, buffer, k, notK, negateNode);
    }else if(child.getKind() == kind::NOT && child[0].getKind() == notK){
      push_back_associative_commute_recursive(child, buffer, notK, k, !negateNode);
    }else{
      if(negateNode){
        buffer.push_back(negate(child));
      }else{
        buffer.push_back(child);
      }
    }
  }
}/* BooleanSimplification::push_back_associative_commute_recursive() */

}/* CVC4 namespace */

