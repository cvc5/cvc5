/*********************                                                        */
/*! \file boolean_simplification.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Simple routines for Boolean simplification
 **
 ** Simple, commonly-used routines for Boolean simplification.
 **/

#include "smt_util/boolean_simplification.h"

namespace CVC4 {

bool BooleanSimplification::push_back_associative_commute_recursive(
    Node n, std::vector<Node>& buffer, Kind k, Kind notK, bool negateNode)
{
  Node::iterator i = n.begin(), end = n.end();
  for(; i != end; ++i){
    Node child = *i;
    if(child.getKind() == k){
      if(! push_back_associative_commute_recursive(child, buffer, k, notK, negateNode)) {
        return false;
      }
    }else if(child.getKind() == kind::NOT && child[0].getKind() == notK){
      if(! push_back_associative_commute_recursive(child[0], buffer, notK, k, !negateNode)) {
        return false;
      }
    }else{
      if(negateNode){
        if(child.isConst()) {
          if((k == kind::AND && child.getConst<bool>()) ||
             (k == kind::OR && !child.getConst<bool>())) {
            buffer.clear();
            buffer.push_back(negate(child));
            return false;
          }
        } else {
          buffer.push_back(negate(child));
        }
      }else{
        if(child.isConst()) {
          if((k == kind::OR && child.getConst<bool>()) ||
             (k == kind::AND && !child.getConst<bool>())) {
            buffer.clear();
            buffer.push_back(child);
            return false;
          }
        } else {
          buffer.push_back(child);
        }
      }
    }
  }
  return true;
}/* BooleanSimplification::push_back_associative_commute_recursive() */

}/* CVC4 namespace */
