/*********************                                                        */
/*! \file nl_iand_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for processing lemmas from the non-linear solver
 **/

#ifndef CVC4__THEORY__ARITH__NL__NL_IAND_UTILS_H
#define CVC4__THEORY__ARITH__NL__NL_IAND_UTILS_H

#include <tuple>
#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

class IAndHelper {

 public:
  
  /**
   * A generic function that creates a node that represents a bitwise
   * operation.
   *
   * For example: Suppose bvsize is 4, granularity is 1, and f(x,y) = x && y.
   * Denote by ITE(a,b) the term: ite(a==0, 0, ite(b==1, 1, 0)).
   * The result of this function would be:
   * ITE(x[0], y[0])*2^0 + ... + ITE(x[3], y[3])*2^3
   *
   * For another example: Suppose bvsize is 4, granularity is 2,
   * and f(x,y) = x && y.
   * Denote by ITE(a,b) the term that corresponds to the following table:
   * a | b |  ITE(a,b)
   * ----------------
   * 0 | 0 | 0
   * 0 | 1 | 0
   * 0 | 2 | 0
   * 0 | 3 | 0
   * 1 | 0 | 0
   * 1 | 1 | 1
   * 1 | 2 | 0
   * 1 | 3 | 1
   * 2 | 0 | 0
   * 2 | 1 | 0
   * 2 | 2 | 2
   * 2 | 3 | 2
   * 3 | 0 | 0
   * 3 | 1 | 1
   * 3 | 2 | 2
   * 3 | 3 | 3
   *
   * For example, 2 in binary is 10 and 1 in binary is 01, and so doing
   * "bitwise f" on them gives 00.
   * The result of this function would be:
   * ITE(x[1:0], y[1:0])*2^0 + ITE(x[3:2], y[3:2])*2^2
   *
   *
   * @param x is an integer operand that correspond to the first original
   *        bit-vector operand.
   * @param y is an integer operand that correspond to the second original
   *        bit-vector operand.
   * @param bvsize is the bit width of the original bit-vector variables.
   * @param granularity is specified in the options for this preprocessing
   *        pass.
   * @param f is a pointer to a boolean function that corresponds
   *        to the original bitwise operation.
   * @return A node that represents the operation, as described above.
   */
  Node createBitwiseNode(Node x,
                                Node y,
                                uint64_t bvsize,
			 uint64_t granularity);

  /**
   * A helper function for createBitwiseNode
   * @param x integer node corresponding to the original first bit-vector
   *        argument
   * @param y integer node corresponding to the original second bit-vector
   *        argument nodes.
   * @param granularity the bitwidth of the original bit-vector nodes.
   * @param table a function from pairs of integers to integers.
   *        The domain of this function consists of pairs of
   *        integers between 0 (inclusive) and 2^{bitwidth} (exclusive).
   * @return An ite term that represents this table.
   */
  Node createITEFromTable(
      Node x,
      Node y,
      uint64_t granularity,
      std::map<std::pair<int64_t, int64_t>, int64_t> table);


  Node createPart(Node x, Node y, uint64_t granularity);
  std::map<std::pair<int64_t, int64_t>, int64_t> getAndTable(uint64_t granularity);
  void addDefaultValue(std::map<std::pair<int64_t, int64_t>, int64_t>& table, int64_t num_of_values);

  std::map<int64_t, std::map<std::pair<int64_t, int64_t>, int64_t >> d_bvandTable;
  
};
  
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NL_IAND_UTILS_H */
