/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for data types.
 */

#ifndef CVC5__THEORY__DATATYPES__UTILS_H
#define CVC5__THEORY__DATATYPES__UTILS_H

#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace datatypes {

class DatatypesUtils
{
 public:
  /**
   * @param tuple a node of tuple type
   * @param n_th the index of the element to be extracted, and must satisfy the
   * constraint 0 <= n_th < length of tuple.
   * @return tuple element at index n_th
   */
  static Node nthElementOfTuple(Node tuple, int n_th);

  static std::vector<Node> getTupleElements();

  /**
   * @param tuple a tuple node of the form (tuple e_1 ... e_n)
   * @return the reverse of the argument, i.e., (tuple e_n ... e_1)
   */
  static Node reverseTuple(Node tuple);
};
}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__DATATYPES__UTILS_H */
