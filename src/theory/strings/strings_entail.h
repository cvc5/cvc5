/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Entailment tests involving strings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__STRING_ENTAIL_H
#define CVC5__THEORY__STRINGS__STRING_ENTAIL_H

#include <vector>

#include "expr/node.h"
#include "theory/strings/arith_entail.h"

namespace cvc5::internal {
namespace theory {

class Rewriter;

namespace strings {

class SequencesRewriter;

/**
 * Entailment tests involving strings.
 * Some of these techniques are described in Reynolds et al, "High Level
 * Abstractions for Simplifying Extended String Constraints in SMT", CAV 2019.
 */
class StringsEntail
{
 public:
  StringsEntail(Rewriter* r, ArithEntail& aent, SequencesRewriter& rewriter);

  /** can constant contain list
   * return true if constant c can contain the list l in order
   * firstc/lastc store which indices in l were used to determine the return
   * value.
   *   (This is typically used when this function returns false, for minimizing
   * explanations)
   *
   * For example:
   *   canConstantContainList( "abc", { x, "c", y } ) returns true
   *     firstc/lastc are updated to 1/1
   *   canConstantContainList( "abc", { x, "d", y } ) returns false
   *     firstc/lastc are updated to 1/1
   *   canConstantContainList( "abcdef", { x, "b", y, "a", z, "c", w }
   *     returns false
   *     firstc/lastc are updated to 1/3
   *   canConstantContainList( "abcdef", { x, "b", y, "e", z, "c", w }
   *     returns false
   *     firstc/lastc are updated to 1/5
   */
  static bool canConstantContainList(Node c,
                                     std::vector<Node>& l,
                                     int& firstc,
                                     int& lastc);
  /** can constant contain concat
   * same as above but with n = str.++( l ) instead of l
   */
  bool canConstantContainConcat(Node c, Node n, int& firstc, int& lastc);

  /** strip symbolic length
   *
   * This function strips off components of n1 whose length is less than or
   * equal to argument curr, and stores them in nr. The direction dir
   * determines whether the components are removed from the start or end of n1.
   * If `strict` is set to true, then the function only returns true if full
   * length `curr` can be stripped.
   *
   * In detail, this function updates n1 to n1' such that:
   *   If dir=1,
   *     n1 = str.++( nr, n1' )
   *   If dir=-1
   *     n1 = str.++( n1', nr )
   * It updates curr to curr' such that:
   *   curr' = curr - str.len( str.++( nr ) ), and
   *   curr' >= 0
   * where the latter fact is determined by checkArithEntail.
   *
   * This function returns true if n1 is modified.
   *
   * For example:
   *
   *  stripSymbolicLength( { x, "abc", y }, {}, 1, str.len(x)+1 )
   *    returns true
   *    n1 is updated to { "bc", y }
   *    nr is updated to { x, "a" }
   *    curr is updated to 0   *
   *
   * stripSymbolicLength( { x, "abc", y }, {}, 1, str.len(x)-1 )
   *    returns false
   *
   *  stripSymbolicLength( { y, "abc", x }, {}, 1, str.len(x)+1 )
   *    returns false
   *
   *  stripSymbolicLength( { x, "abc", y }, {}, -1, 2*str.len(y)+4 )
   *    returns true
   *    n1 is updated to { x }
   *    nr is updated to { "abc", y }
   *    curr is updated to str.len(y)+1
   */
  bool stripSymbolicLength(std::vector<Node>& n1,
                           std::vector<Node>& nr,
                           int dir,
                           Node& curr,
                           bool strict = false);
  /** component contains
   * This function is used when rewriting str.contains( t1, t2 ), where
   * n1 is the vector form of t1
   * n2 is the vector form of t2
   *
   * If this function returns n>=0 for some n, then
   *    n1 = { x1...x{n-1} xn...x{n+s} x{n+s+1}...xm },
   *    n2 = { y1...ys },
   *    y1 is a suffix of xn,
   *    y2...y{s-1} = x{n+1}...x{n+s-1}, and
   *    ys is a prefix of x{n+s}
   * Otherwise it returns -1.
   *
   * This function may update n1 if computeRemainder = true.
   *   We maintain the invariant that the resulting value n1'
   *   of n1 after this function is such that:
   *     n1 = str.++( nb, n1', ne )
   * The vectors nb and ne have the following properties.
   * If computeRemainder = true, then
   *   If remainderDir != -1, then
   *     ne is { x{n+s}' x{n+s+1}...xm }
   *     where x{n+s} = str.++( ys, x{n+s}' ).
   *   If remainderDir != 1, then
   *     nb is { x1, ..., x{n-1}, xn' }
   *     where xn = str.++( xn', y1 ).
   *
   * For example:
   *
   * componentContains({ x, "abc", x }, { "b" }, {}, true, 0)
   *   returns 1,
   *   n1 is updated to { "b" },
   *   nb is updated to { x, "a" },
   *   ne is updated to { "c", x }
   *
   * componentContains({ x, "abc", x }, { "b" }, {}, true, 1)
   *   returns 1,
   *   n1 is updated to { x, "ab" },
   *   ne is updated to { "c", x }
   *
   * componentContains({ y, z, "abc", x, "def" }, { "c", x, "de" }, {}, true, 1)
   *   returns 2,
   *   n1 is updated to { y, z, "abc", x, "de" },
   *   ne is updated to { "f" }
   *
   * componentContains({ y, "abc", x, "def" }, { "c", x, "de" }, {}, true, -1)
   *   returns 1,
   *   n1 is updated to { "c", x, "def" },
   *   nb is updated to { y, "ab" }
   *
   * Note that when computeRemainder is true, this check is less aggressive.
   * In particular, the only terms we add to nb and ne are terms from n1 or
   * substrings of words that appear in n1. If we would require constructing
   * a (symbolic) substring term, we fail instead. For example:
   *
   * componentContains({ y }, { substr(y,0,1) }, {}, false, 1) returns 1,
   * while componentContains({ y }, { substr(y,0,1) }, {}, true, 1) returns 0;
   * it does not return 1 updating nb/ne to
   * { substr(y,0,1) } / { substr(y,1,len(y)-1) }. This is to avoid
   * non-termination in the rewriter.
   */
  int componentContains(std::vector<Node>& n1,
                        std::vector<Node>& n2,
                        std::vector<Node>& nb,
                        std::vector<Node>& ne,
                        bool computeRemainder = false,
                        int remainderDir = 0);
  /** strip constant endpoints
   * This function is used when rewriting str.contains( t1, t2 ), where
   * n1 is the vector form of t1
   * n2 is the vector form of t2
   *
   * It modifies n1 to a new vector n1' such that:
   * (1) str.contains( str.++( n1 ), str.++( n2 ) ) is equivalent to
   * str.contains( str.++( n1' ), str.++( n2 ) )
   * (2) str.++( n1 ) = str.++( nb, n1', ne )
   *
   * "dir" is the direction in which we can modify n1:
   * if dir = 1, then we allow dropping components from the front of n1,
   * if dir = -1, then we allow dropping components from the back of n1,
   * if dir = 0, then we allow dropping components from either.
   *
   * It returns true if n1 is modified.
   *
   * For example:
   * stripConstantEndpoints({ "ab", x, "de" }, { "c" }, {}, {}, 1)
   *   returns true,
   *   n1 is updated to { x, "de" }
   *   nb is updated to { "ab" }
   * stripConstantEndpoints({ "ab", x, "de" }, { "bd" }, {}, {}, 0)
   *   returns true,
   *   n1 is updated to { "b", x, "d" }
   *   nb is updated to { "a" }
   *   ne is updated to { "e" }
   * stripConstantEndpoints({ "ad", substr("ccc",x,y) }, { "d" }, {}, {}, -1)
   *   returns true,
   *   n1 is updated to {"ad"}
   *   ne is updated to { substr("ccc",x,y) }
   */
  static bool stripConstantEndpoints(std::vector<Node>& n1,
                                     std::vector<Node>& n2,
                                     std::vector<Node>& nb,
                                     std::vector<Node>& ne,
                                     int dir = 0);

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
  Node checkContains(Node a, Node b, bool fullRewriter = true);

  /** entail non-empty
   *
   * Checks whether string a is entailed to be non-empty. Is equivalent to
   * the call checkArithEntail( len( a ), true ).
   */
  bool checkNonEmpty(Node a);

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
  bool checkLengthOne(Node s, bool strict = false);

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
  Node getStringOrEmpty(Node n);

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
  Node inferEqsFromContains(Node x, Node y);

 private:
  /** component contains base
   *
   * This function is a helper for the above function.
   *
   * It returns true if n2 is contained in n1 with the following
   * restrictions:
   *   If dir=1, then n2 must be a suffix of n1.
   *   If dir=-1, then n2 must be a prefix of n1.
   *
   * If computeRemainder is true, then n1rb and n1re are
   * updated such that :
   *   n1 = str.++( n1rb, n2, n1re )
   * where a null value of n1rb and n1re indicates the
   * empty string.
   *
   * For example:
   *
   * componentContainsBase("cabe", "ab", n1rb, n1re, 1, false)
   *   returns false.
   *
   * componentContainsBase("cabe", "ab", n1rb, n1re, 0, true)
   *   returns true,
   *   n1rb is set to "c",
   *   n1re is set to "e".
   *
   * componentContainsBase(y, str.substr(y,0,5), n1rb, n1re, -1, true)
   *   returns true,
   *   n1re is set to str.substr(y,5,str.len(y)).
   *
   *
   * Notice that this function may return false when it cannot compute a
   * remainder when it otherwise would have returned true. For example:
   *
   * componentContainsBase(y, str.substr(y,x,z), n1rb, n1re, 0, false)
   *   returns true.
   *
   * Hence, we know that str.substr(y,x,z) is contained in y. However:
   *
   * componentContainsBase(y, str.substr(y,x,z), n1rb, n1re, 0, true)
   *   returns false.
   *
   * The reason is since computeRemainder=true, it must be that
   *   y = str.++( n1rb, str.substr(y,x,z), n1re )
   * for some n1rb, n1re. However, to construct such n1rb, n1re would require
   * e.g. the terms:
   *   y = str.++( ite( x+z < 0 OR x < 0, "", str.substr(y,0,x) ),
   *               str.substr(y,x,z),
   *               ite( x+z < 0 OR x < 0, y, str.substr(y,x+z,len(y)) ) )
   *
   * Since we do not wish to introduce new (symbolic) terms, we
   * instead return false, indicating that we cannot compute the remainder.
   */
  bool componentContainsBase(
      Node n1, Node n2, Node& n1rb, Node& n1re, int dir, bool computeRemainder);
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

 private:
  /** Pointer to the full rewriter */
  Rewriter* d_rr;
  /** The arithmetic entailment module */
  ArithEntail& d_arithEntail;
  /**
   * Reference to the sequences rewriter that owns this `StringsEntail`
   * instance.
   */
  SequencesRewriter& d_rewriter;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__STRING_ENTAIL_H */
