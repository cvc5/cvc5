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

#ifndef CVC5__THEORY__TUPLE__UTILS_H
#define CVC5__THEORY__TUPLE__UTILS_H

#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace datatypes {

class TupleUtils
{
 public:
  /**
   * @param tuple a node of tuple type
   * @param n_th the index of the element to be extracted, and must satisfy the
   * constraint 0 <= n_th < length of tuple.
   * @return tuple element at index n_th
   */
  static Node nthElementOfTuple(Node tuple, int n_th);

  /**
   * @param tuple a tuple node of the form (tuple a_1 ... a_n)
   * @return the vector [a_1, ... a_n]
   */
  static std::vector<Node> getTupleElements(Node tuple);

  /**
   * @param tuple1 a tuple node of the form (tuple a_1 ... a_n)
   * @param tuple2 a tuple node of the form (tuple b_1 ... b_n)
   * @return the vector [a_1, ... a_n, b_1, ... b_n]
   */
  static std::vector<Node> getTupleElements(Node tuple1, Node tuple2);

  /**
   * construct a tuple from a list of elements
   * @param tupleType the type of the returned tuple
   * @param elements the list of nodes
   * @param start the index of the first element
   * @param end the index of the last element
   * @pre the elements from start to end should match the tuple type
   * @return a tuple of constructed from elements from start to end
   */
  static Node constructTupleFromElements(TypeNode tupleType,
                                         const std::vector<Node>& elements,
                                         size_t start,
                                         size_t end);

  /**
   * construct a flattened tuple from two tuples
   * @param tupleType the type of the returned tuple
   * @param tuple1 a tuple node of the form (tuple a_1 ... a_n)
   * @param tuple2 a tuple node of the form (tuple b_1 ... b_n)
   * @pre the elements of tuple1, tuple2 should match the tuple type
   * @return  (tuple a1 ... an b1 ... bn)
   */
  static Node concatTuples(TypeNode tupleType, Node tuple1, Node tuple2);

  /**
   * @param tuple a tuple node of the form (tuple e_1 ... e_n)
   * @return the reverse of the argument, i.e., (tuple e_n ... e_1)
   */
  static Node reverseTuple(Node tuple);
};
}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__TUPLE__UTILS_H */
