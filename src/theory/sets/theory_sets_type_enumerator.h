/*********************                                                        */
/*! \file theory_sets_type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King, Andrew Reynolds, Mudathir Mahgoub
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief type enumerator for sets
 **
 ** A set enumerator that iterates over the power set of the element type
 ** starting with the empty set as the initial value
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__TYPE_ENUMERATOR_H
#define CVC4__THEORY__SETS__TYPE_ENUMERATOR_H

#include "expr/kind.h"
#include "expr/type_node.h"
#include "theory/rewriter.h"
#include "theory/sets/normal_form.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace sets {

class SetEnumerator : public TypeEnumeratorBase<SetEnumerator>
{
 public:
  SetEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr);
  SetEnumerator(const SetEnumerator& enumerator);
  ~SetEnumerator();

  Node operator*() override;

  /**
   * This operator iterates over the power set of the element type
   * following the order of a bitvector counter.
   * Example: iterating over a set of bitvecotors of length 2 will return the
   * following sequence consisting of 16 sets:
   * {}, {00}, {01}, {00, 01}, {10}, {00, 10}, {01, 10}, {00, 01, 10}, ...,
   * {00, 01, 10, 11}
   */
  SetEnumerator& operator++() override;

  bool isFinished() override;

 private:
  NodeManager* d_nodeManager;
  TypeEnumerator d_elementEnumerator;
  bool d_isFinished;
  std::vector<Node> d_elementsSoFar;
  unsigned int d_currentSetIndex;
  Node d_currentSet;
}; /* class SetEnumerator */

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SETS__TYPE_ENUMERATOR_H */
