/*********************                                                        */
/*! \file theory_bags_type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief type enumerator for bags
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__TYPE_ENUMERATOR_H
#define CVC4__THEORY__BAGS__TYPE_ENUMERATOR_H

#include "expr/type_node.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace bags {

class BagEnumerator : public TypeEnumeratorBase<BagEnumerator>
{
 public:
  BagEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr);
  BagEnumerator(const BagEnumerator& enumerator);
  ~BagEnumerator();

  Node operator*() override;

  /**
   * This operator iterates over the infinite bags constructed from the element
   * type . Ideally iterating over bags of {1, 2, 3, ...} will return the
   * following infinite sequence of bags, where n in the pair (m, n) means the
   * multiplicity of the element m in the bag
   * {},                    sum = 0, #elements = 0, cardinality = 0
   *
   * {(1,1)},               sum = 2, #elements = 1, cardinality = 1
   *
   * {(2,1)},               sum = 3, #elements = 2, cardinality = 1
   * {(1,2)},               sum = 3, #elements = 2, cardinality = 2
   *
   * {(3, 1)},              sum = 4, #elements = 3, cardinality = 1
   * {(2, 2)},              sum = 4, #elements = 3, cardinality = 2
   * {(1, 3)},              sum = 4, #elements = 3, cardinality = 3
   *
   * {(4, 1)},              sum = 5, #elements = 4, cardinality = 1
   * {(3, 2)},              sum = 5, #elements = 4, cardinality = 2
   * {(1, 1),(2, 1)},       sum = 5, #elements = 4, cardinality = 2
   * {(2, 3)},              sum = 5, #elements = 4, cardinality = 3
   * {(1, 4)},              sum = 5, #elements = 4, cardinality = 4
   *
   * {(5, 1)},              sum = 6, #elements = 5, cardinality = 1
   * {(4, 2)},              sum = 6, #elements = 5, cardinality = 2
   * {(1, 1), (3,1)},       sum = 6, #elements = 5, cardinality = 2
   * {(3, 3)},              sum = 6, #elements = 5, cardinality = 3
   * {(1, 1), (2,2)},       sum = 6, #elements = 5, cardinality = 3
   * {(1, 2), (2,1)},       sum = 6, #elements = 5, cardinality = 3
   * {(2, 4)},              sum = 6, #elements = 5, cardinality = 4
   * {(1, 5)},              sum = 6, #elements = 5, cardinality = 5
   *
   * This seems too expensive to implement.
   * For now we are implementing an obvious solution
   * {(1,1)}, {(1,2)}, {(1,3)}, ... which works for both fininte and infinite
   * types
   */
  BagEnumerator& operator++() override;

  bool isFinished() override;

 private:
  /** a pointer to the node manager */
  NodeManager* d_nodeManager;
  /** an enumerator for the set of pairs of element type x integer type */
  TypeEnumerator d_elementTypeEnumerator;
  /** the current set returned by the set enumerator */
  Node d_currentBag;
  /** the first value returned by the element type enumerator*/
  Node d_element;
}; /* class BagEnumerator */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__TYPE_ENUMERATOR_H */