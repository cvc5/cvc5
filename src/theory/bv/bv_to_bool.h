/*********************                                                        */
/*! \file bv_to_bool.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
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
#include "theory/bv/theory_bv_utils.h"

#ifndef __CVC4__THEORY__BV__BV_TO_BOOL_H
#define __CVC4__THEORY__BV__BV_TO_BOOL_H

namespace CVC4 {
namespace theory {
namespace bv {

typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction> TNodeSet; 
typedef __gnu_cxx::hash_map<Node, Node, TNodeHashFunction> NodeNodeMap; 

class BvToBoolVisitor {
  NodeNodeMap d_bvToBoolMap; 
  NodeNodeMap d_cache;
  Node d_one;
  Node d_zero;

  void addToCache(TNode term, Node new_term);
  Node getCache(TNode term) const;
  bool hasCache(TNode term) const; 
  
  bool isConvertibleBvTerm(TNode node);
  bool isConvertibleBvAtom(TNode node);
  Node getBoolForBvTerm(TNode node);
  Node convertBvAtom(TNode node);
  Node convertBvTerm(TNode node);
  void check(TNode current, TNode parent);
public:
  typedef Node return_type;
  BvToBoolVisitor()
    : d_bvToBoolMap(), 
      d_cache(),
      d_one(utils::mkConst(BitVector(1, 1u))),
      d_zero(utils::mkConst(BitVector(1, 0u)))
  {}
  void start(TNode node);
  bool alreadyVisited(TNode current, TNode parent);
  void visit(TNode current, TNode parent);
  return_type done(TNode node);
  void storeBvToBool(TNode bv_term, TNode bool_term);
  bool hasBoolTerm(TNode node); 
}; 


class BvToBoolPreprocessor {
  bool matchesBooleanPatern(TNode node);
public:
  BvToBoolPreprocessor()
  {}
  ~BvToBoolPreprocessor() {}
  void liftBoolToBV(const std::vector<Node>& assertions, std::vector<Node>& new_assertions);
}; 


}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */


#endif /* __CVC4__THEORY__BV__BV_TO_BOOL_H */
