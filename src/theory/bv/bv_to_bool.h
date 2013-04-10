/*********************                                                        */
/*! \file bv_to_bool.h
 ** \verbatim
 ** Original author: Liana Hadarean 
 ** Major contributors: None. 
 ** Minor contributors (to current version): None. 
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Preprocessing pass that lifts bit-vectors of size 1 to booleans.
 **
 ** Preprocessing pass that lifts bit-vectors of size 1 to booleans. 
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__BV_TO_BOOL_H
#define __CVC4__THEORY__BV__BV_TO_BOOL_H

namespace CVC4 {
namespace theory {
namespace bv {

class BvToBoolVisitor {
  typedef unsigned return_type;
  typedef __gnu_cxx::hash_set<TNode> TNodeSet; 
  typedef __gnu_cxx::hash_map<TNode, Node> TNodeNodeMap; 
  TNodeNodeMap d_bvToBool;
  TNodeSet d_visited;
  Node d_one;
  Node d_zero;

  void addBvToBool(TNode bv_term, Node bool_term);
  Node toBoolTerm(TNode bv_term) const;
  bool hasBoolTerm(TNode bv_term) const; 
  
public:
  BvToBoolVisitor()
    : d_substitution(),
      d_visited,
      d_one(utils::mkConst(BitVector(1, 1u))),
      d_zero(utils::mkConst(BitVector(1, 0u)))
  {}
  void start(TNode node);
  bool alreadyVisited(TNode current, TNode parent);
  void visit(TNode current, TNode parent);
  return_type done(TNode node);
  Node liftBoolToBV(TNode node);
  
}; 

class BvToBoolPreprocessor {
  BvToBoolVisitor d_visitor; 
public:
  BvToBoolPreprocessor()
    : d_visitor
  {}
  ~BvToBoolPreprocessor() {}
  Node liftBvToBool(TNode assertion); 
}; 


}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */


#endif /* __CVC4__THEORY__BV__BV_TO_BOOL_H */
