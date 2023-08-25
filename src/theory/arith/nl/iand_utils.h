/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Makai Mann, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities to maintain finite tables that represent the value of iand.
 */

#ifndef CVC5__THEORY__ARITH__IAND_TABLE_H
#define CVC5__THEORY__ARITH__IAND_TABLE_H

#include <map>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

/**
 * A class that computes tables for iand values
 * with various bit-widths
 */
class IAndUtils
{
 public:
  IAndUtils();

  /**
   * A generic function that creates a node that represents a bvand
   * operation.
   *
   * For example: Suppose bvsize is 4, granularity is 1.
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
   * More precisely, the ITE term is optimized so that the most common
   * result is in the final "else" branch.
   * Hence in practice, the generated ITEs will be shorter.
   *
   * @param x is an integer operand that correspond to the first original
   *        bit-vector operand.
   * @param y is an integer operand that correspond to the second original
   *        bit-vector operand.
   * @param bvsize is the bit width of the original bit-vector variables.
   * @param granularity is specified in the options for this preprocessing
   *        pass.
   * @return A node that represents the operation, as described above.
   */
  Node createSumNode(Node x, Node y, uint32_t bvsize, uint32_t granularity);

  /** Create a bitwise integer And node for two integers x and y for bits
   *  between hgih and low Example for high = 0, low = 0 (e.g. granularity 1)
   *    ite(x[0] == 1 & y[0] == 1, #b1, #b0)
   *
   *  It makes use of computeAndTable
   *
   *  @param x an integer operand corresponding to the first original
   *         bit-vector operand
   *  @param y an integer operand corresponding to the second original
   *         bit-vector operand
   *  @param high the upper bit index
   *  @param low the lower bit index
   *  @return an integer node corresponding to a bitwise AND applied to
   *          integers for the bits between high and low
   */
  Node createBitwiseIAndNode(Node x, Node y, uint32_t high, uint32_t low);

  /** extract from integer
   *  ((_ extract i j) n) is n / 2^j mod 2^{i-j+1}
   */
  Node iextract(uint32_t i, uint32_t j, Node n) const;

  // Helpers

  /**
   * A helper function for createSumNode and createBitwiseIAndNode
   * @param x integer node corresponding to the original first bit-vector
   *        argument
   * @param y integer node corresponding to the original second bit-vector
   *        argument nodes.
   * @param granularity the bitwidth of the original bit-vector nodes.
   * @param table a function from pairs of integers to integers.
   *        The domain of this function consists of pairs of
   *        integers between 0 (inclusive) and 2^{bitwidth} (exclusive).
   *        The domain also includes one additional pair (-1, -1), that
   *        represents the default (most common) value.
   * @return An ite term that represents this table.
   */
  Node createITEFromTable(
      Node x,
      Node y,
      uint32_t granularity,
      const std::map<std::pair<int64_t, int64_t>, uint64_t>& table);

  /**
   * updates  d_bvandTable[granularity] if it wasn't already computed.
   */
  void computeAndTable(uint32_t granularity);

  /**
   * @param table a table that represents integer conjunction
   * @param num_of_values the number of rows in the table
   * The function will add a single row to the table.
   * the key will be (-1, -1) and the value will be the most common
   * value of the original table.
   */
  void addDefaultValue(std::map<std::pair<int64_t, int64_t>, uint64_t>& table,
                       uint64_t num_of_values);

  /** 2^k */
  Node twoToK(unsigned k) const;

  /** 2^k-1 */
  Node twoToKMinusOne(unsigned k) const;

  /**
   * For each granularity between 1 and 8, we store a separate table
   * in d_bvandTable[granularity].
   * The definition of these tables is given in the description of
   * createSumNode.
   */
  std::map<uint64_t, std::map<std::pair<int64_t, int64_t>, uint64_t>>
      d_bvandTable;

 private:
  /** commonly used terms */
  Node d_zero;
  Node d_one;
  Node d_two;
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__IAND_TABLE_H */
