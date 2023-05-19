/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic utilities regarding monomial sums.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__MSUM_H
#define CVC5__THEORY__ARITH__MSUM_H

#include <map>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {

/** Arithmetic utilities regarding monomial sums.
 *
 * Note the following terminology:
 *
 *   We say Node c is a {monomial constant} (or m-constant) if either:
 *   (a) c is a constant Rational, or
 *   (b) c is null.
 *
 *   We say Node v is a {monomial variable} (or m-variable) if either:
 *   (a) v.getType().isRealOrInt() and v is not a constant, or
 *   (b) v is null.
 *
 *   For m-constant or m-variable t, we write [t] to denote 1 if t.isNull() and
 *   t otherwise.
 *
 *   A monomial m is a pair ( mvariable, mconstant ) of the form ( v, c ), which
 *   is interpreted as [c]*[v].
 *
 *   A {monmoial sum} msum is represented by a std::map< Node, Node > having
 *   key-value pairs of the form ( mvariable, mconstant ).
 *   It is interpreted as:
 *   [msum] = sum_{( v, c ) \in msum } [c]*[v]
 *   It is critical that this map is ordered so that operations like adding
 *   two monomial sums can be done efficiently. The ordering itself is not
 *   important, and currently corresponds to the default ordering on Nodes.
 *
 * The following has utilities involving monmoial sums.
 *
 */
class ArithMSum
{
 public:
  /** get monomial
   *
   * If n = n[0]*n[1] where n[0] is constant and n[1] is not,
   * this function returns true, sets c to n[0] and v to n[1].
   */
  static bool getMonomial(Node n, Node& c, Node& v);

  /** get monomial
   *
   * If this function returns true, it adds the ( m-constant, m-variable )
   * pair corresponding to the monomial representation of n to the
   * monomial sum msum.
   *
   * This function returns false if the m-variable of n is already
   * present in n.
   */
  static bool getMonomial(Node n, std::map<Node, Node>& msum);

  /** get monomial sum for real-valued term n
   *
   * If this function returns true, it sets msum to a monmoial sum such that
   *   [msum] is equivalent to n
   *
   * This function may return false if n is not a sum of monomials
   * whose variables are pairwise unique.
   * If term n is in rewritten form, this function should always return true.
   */
  static bool getMonomialSum(Node n, std::map<Node, Node>& msum);

  /** get monmoial sum literal for literal lit
   *
   * If this function returns true, it sets msum to a monmoial sum such that
   *   [msum] <k> 0  is equivalent to lit[0] <k> lit[1]
   * where k is the Kind of lit, one of { EQUAL, GEQ }.
   *
   * This function may return false if either side of lit is not a sum
   * of monomials whose variables are pairwise unique on that side.
   * If literal lit is in rewritten form, this function should always return
   * true.
   */
  static bool getMonomialSumLit(Node lit, std::map<Node, Node>& msum);

  /** make node for monomial sum
   *
   * Make the Node corresponding to the interpretation of msum, [msum], where:
   *   [msum] = sum_{( v, c ) \in msum } [c]*[v]
   *
   * @param msum The monomial sum
   * @return The node corresponding to the monomial sum
   *
   * Note this utility is agnostic to types, it will return the integer 0 if
   * msum is empty.
   */
  static Node mkNode(const std::map<Node, Node>& msum);

  /** make coefficent term
   *
   * Input c is a m-constant.
   * Returns the term t if c.isNull() or c*t otherwise.
   */
  static inline Node mkCoeffTerm(Node c, Node t)
  {
    return c.isNull() ? t : NodeManager::currentNM()->mkNode(kind::MULT, c, t);
  }

  /** isolate variable v in constraint ([msum] <k> 0)
   *
   * If this function returns a value ret where ret != 0, then
   * veq_c is set to m-constant, and val is set to a term such that:
   *    If ret=1, then ([veq_c] * v <k> val) is equivalent to [msum] <k> 0.
   *   If ret=-1, then (val <k> [veq_c] * v) is equivalent to [msum] <k> 0.
   *   If veq_c is non-null, then it is a positive constant Rational.
   * The returned value of veq_c is only non-null if v has integer type.
   *
   * This function returns 0, indicating a failure, if msum does not contain
   * a (non-zero) monomial having mvariable v.
   */
  static int isolate(
      Node v, const std::map<Node, Node>& msum, Node& veq_c, Node& val, Kind k);

  /** isolate variable v in constraint ([msum] <k> 0)
   *
   * If this function returns a value ret where ret != 0, then veq
   * is set to a literal that is equivalent to ([msum] <k> 0), and:
   *    If ret=1, then veq is of the form ( v <k> val) if veq_c.isNull(),
   *                   or ([veq_c] * v <k> val) if !veq_c.isNull().
   *   If ret=-1, then veq is of the form ( val <k> v) if veq_c.isNull(),
   *                   or (val <k> [veq_c] * v) if !veq_c.isNull().
   * If doCoeff = false or v does not have Integer type, then veq_c is null.
   *
   * This function returns 0 indicating a failure if msum does not contain
   * a (non-zero) monomial having variable v, or if veq_c must be non-null
   * for an integer constraint and doCoeff is false.
   */
  static int isolate(Node v,
                     const std::map<Node, Node>& msum,
                     Node& veq,
                     Kind k,
                     bool doCoeff = false);

  /** solve equality lit for variable
   *
   * If return value ret is non-null, then:
   *    v = ret is equivalent to lit.
   *
   * This function may return false if lit does not contain v,
   * or if lit is an integer equality with a coefficent on v,
   * e.g. 3*v = 7.
   *
   * Note this utility is agnostic to types, the returned term may be Int when
   * v is Real.
   */
  static Node solveEqualityFor(Node lit, Node v);

  /** decompose real-valued term n
  *
  * If this function returns true, then
  *   ([coeff]*v + rem) is equivalent to n
  * where coeff is non-zero m-constant.
  *
  * This function will return false if n is not a monomial sum containing
  * a monomial with factor v.
  */
  static bool decompose(Node n, Node v, Node& coeff, Node& rem);

  /** debug print for a monmoial sum, prints to Trace(c) */
  static void debugPrintMonomialSum(std::map<Node, Node>& msum, const char* c);
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__MSUM_H */
