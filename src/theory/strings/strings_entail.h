/*********************                                                        */
/*! \file strings_entail.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Entailment tests involving strings
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__STRING_ENTAIL_H
#define CVC4__THEORY__STRINGS__STRING_ENTAIL_H

#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace strings {

/** 
 * Entailment tests involving strings.
 * Some of these techniques are described in Reynolds et al, "High Level
 * Abstractions for Simplifying Extended String Constraints in SMT", CAV 2019.
 */
class StringsEntail
{
public:
  /**
   * Checks whether a string term `a` is entailed to contain or not contain a
   * string term `b`.
   *
   * @param a The string that is checked whether it contains `b`
   * @param b The string that is checked whether it is contained in `a`
   * @param fullRewriter Determines whether the function can use the full
   * rewriter or only `rewriteContains()` (useful for avoiding loops)
   * @return true node if it can be shown that `a` contains `b`, false node if
   * it can be shown that `a` does not contain `b`, null node otherwise
   */
  static Node checkContains(Node a, Node b, bool fullRewriter = true);

  /** entail non-empty
   *
   * Checks whether string a is entailed to be non-empty. Is equivalent to
   * the call checkArithEntail( len( a ), true ).
   */
  static bool checkNonEmpty(Node a);

  /**
   * Checks whether string has at most/exactly length one. Length one strings
   * can be used for more aggressive rewriting because there is guaranteed that
   * it cannot be overlap multiple components in a string concatenation.
   *
   * @param s The string to check
   * @param strict If true, the string must have exactly length one, otherwise
   * at most length one
   * @return True if the string has at most/exactly length one, false otherwise
   */
  static bool checkLengthOne(Node s, bool strict = false);

  /**
   * Checks whether it is always true that `a` is a strict subset of `b` in the
   * multiset domain.
   *
   * Examples:
   *
   * a = (str.++ "A" x), b = (str.++ "A" x "B") ---> true
   * a = (str.++ "A" x), b = (str.++ "B" x "AA") ---> true
   * a = (str.++ "A" x), b = (str.++ "B" y "AA") ---> false
   *
   * @param a The term for which it should be checked if it is a strict subset
   * of `b` in the multiset domain
   * @param b The term for which it should be checked if it is a strict
   * superset of `a` in the multiset domain
   * @return True if it is always the case that `a` is a strict subset of `b`,
   * false otherwise.
   */
  static bool checkMultisetSubset(Node a, Node b);

  /**
   * Returns a character `c` if it is always the case that str.in.re(a, c*),
   * i.e. if all possible values of `a` only consist of `c` characters, and the
   * null node otherwise. If `a` is the empty string, the function returns an
   * empty string.
   *
   * @param a The node to check for homogeneity
   * @return If `a` is homogeneous, the only character that it may contain, the
   * empty string if `a` is empty, and the null node otherwise
   */
  static Node checkHomogeneousString(Node a);

  /**
   * Simplifies a given node `a` s.t. the result is a concatenation of string
   * terms that can be interpreted as a multiset and which contains all
   * multisets that `a` could form.
   *
   * Examples:
   *
   * (str.substr "AA" 0 n) ---> "AA"
   * (str.replace "AAA" x "BB") ---> (str.++ "AAA" "BB")
   *
   * @param a The node to simplify
   * @return A concatenation that can be interpreted as a multiset
   */
  static Node getMultisetApproximation(Node a);

  /**
   * Overapproximates the possible values of node n. This overapproximation
   * assumes that n can return a value x or the empty string and tries to find
   * the simplest x such that this holds. In the general case, x is the same as
   * the input n. This overapproximation can be used to sort terms with the
   * same possible values in string concatenation for example.
   *
   * Example:
   *
   * getStringOrEmpty( (str.replace "" x y) ) --> y because (str.replace "" x y)
   * either returns y or ""
   *
   * getStringOrEmpty( (str.substr "ABC" x y) ) --> (str.substr "ABC" x y)
   * because the function could not compute a simpler
   */
  static Node getStringOrEmpty(Node n);

  /**
   * Infers a conjunction of equalities that correspond to (str.contains x y)
   * if it can show that the length of y is greater or equal to the length of
   * x. If y is a concatentation, we get x = y1 ++ ... ++ yn, the conjunction
   * is of the form:
   *
   * (and (= x (str.++ y1' ... ym')) (= y1'' "") ... (= yk'' ""))
   *
   * where each yi'' are yi that must be empty for (= x y) to hold and yi' are
   * yi that the function could not infer anything about.  Returns a null node
   * if the function cannot infer that str.len(y) >= str.len(x). Returns (= x
   * y) if the function can infer that str.len(y) >= str.len(x) but cannot
   * infer that any of the yi must be empty.
   */
  static Node inferEqsFromContains(Node x, Node y);
}; 

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__STRING_ENTAIL_H */
