/*********************                                                        */
/*! \file bv_to_bool.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass that lifts bit-vectors of size 1 to booleans.
 **
 ** Preprocessing pass that lifts bit-vectors of size 1 to booleans.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__BV_TO_BOOL_H
#define __CVC4__THEORY__BV__BV_TO_BOOL_H

#include "theory/bv/theory_bv_utils.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace bv {

typedef __gnu_cxx::hash_map<Node, Node, NodeHashFunction> NodeNodeMap;

class BvToBoolPreprocessor {

  struct Statistics {
    IntStat d_numTermsLifted;
    IntStat d_numAtomsLifted;
    IntStat d_numTermsForcedLifted;
    IntStat d_numTermsLowered;
    IntStat d_numAtomsLowered;
    IntStat d_numTermsForcedLowered;
    Statistics();
    ~Statistics();
  };
  
  NodeNodeMap d_liftCache;
  NodeNodeMap d_boolCache;
  Node d_one;
  Node d_zero;

  void addToBoolCache(TNode term, Node new_term);
  Node getBoolCache(TNode term) const;
  bool hasBoolCache(TNode term) const; 

  void addToLiftCache(TNode term, Node new_term);
  Node getLiftCache(TNode term) const;
  bool hasLiftCache(TNode term) const; 
  
  bool isConvertibleBvTerm(TNode node);
  bool isConvertibleBvAtom(TNode node);
  Node convertBvAtom(TNode node);
  Node convertBvTerm(TNode node);
  Node liftNode(TNode current);
  Statistics d_statistics;

  NodeNodeMap d_lowerCache;
  void addToLowerCache(TNode term, Node new_term);
  Node getLowerCache(TNode term) const;
  bool hasLowerCache(TNode term) const; 
  Node lowerNode(TNode current, bool topLevel = false);

public:
  BvToBoolPreprocessor();
  void liftBvToBool(const std::vector<Node>& assertions, std::vector<Node>& new_assertions);
  void lowerBoolToBv(const std::vector<Node>& assertions, std::vector<Node>& new_assertions);
}; 



}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */


#endif /* __CVC4__THEORY__BV__BV_TO_BOOL_H */
