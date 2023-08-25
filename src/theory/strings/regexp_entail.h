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
 * Entailment tests involving regular expressions.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__REGEXP_ENTAIL_H
#define CVC5__THEORY__STRINGS__REGEXP_ENTAIL_H

#include <climits>
#include <utility>
#include <vector>

#include "expr/attribute.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/rewrites.h"
#include "theory/theory_rewriter.h"
#include "theory/type_enumerator.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

class RegExpEntail
{
 public:
  RegExpEntail(Rewriter* r);
  /** simple regular expression consume
   *
   * This method is called when we are rewriting a membership of the form
   *   s1 ++ ... ++ sn in r1 ++ ... ++ rm
   * We have that mchildren consists of the strings s1...sn, and children
   * consists of the regular expressions r1...rm.
   *
   * This method tries to strip off parts of the concatenation terms. It updates
   * the vectors such that the resulting vectors are such that the membership
   * mchildren[n'...n''] in children[m'...m''] is equivalent to the input
   * membership. The argument dir indicates the direction to consider, where
   * 0 means strip off the front, 1 off the back, and < 0 off of both.
   *
   * If this method returns the false node, then we have inferred that no
   * string in the language of r1 ++ ... ++ rm is a prefix (when dir!=1) or
   * suffix (when dir!=0) of s1 ++ ... ++ sn. Otherwise, it returns the null
   * node.
   *
   * For example, given input
   *   mchildren = { "ab", x }, children = { [["a"]], ([["cd"]])* } and dir = 0,
   * this method updates:
   *   mchildren = { "b", x }, children = { ("cd")* }
   * and returns null.
   *
   * For example, given input
   *   { x, "abb", x }, { [[x]], ["a"..."b"], allchar, [[y]], [[x]]} and dir=-1,
   * this method updates:
   *   { "b" }, { [[y]] }
   * where [[.]] denotes str.to.re, and returns null.
   *
   * Notice that the above requirement for returning false is stronger than
   * determining that s1 ++ ... ++ sn in r1 ++ ... ++ rm is equivalent to false.
   * For example, for input "bb" in "b" ++ ( "a" )*, we do not return false
   * since "b" is in the language of "b" ++ ( "a" )* and is a prefix of "bb".
   * We do not return false even though the above membership is equivalent
   * to false. We do this because the function is used e.g. to test whether a
   * possible unrolling leads to a conflict. This is demonstrated by the
   * following examples:
   *
   * For example, given input
   *   { "bb", x }, { "b", ("a")* } and dir=-1,
   * this method updates:
   *   { "b" }, { ("a")* }
   * and returns null.
   *
   * For example, given input
   *   { "cb", x }, { "b", ("a")* } and dir=-1,
   * this method leaves children and mchildren unchanged and returns false.
   *
   * Notice that based on this, we can determine that:
   *   "cb" ++ x  in ( "b" ++ ("a")* )*
   * is equivalent to false, whereas we cannot determine that:
   *   "bb" ++ x  in ( "b" ++ ("a")* )*
   * is equivalent to false.
   */
  static Node simpleRegexpConsume(std::vector<Node>& mchildren,
                                  std::vector<Node>& children,
                                  int dir = -1);
  /**
   * Is t a constant regular expression? A constant regular expression
   * is one with no non-constant (RE or string subterms) and does not contain
   * any non-standard RE terms like re.range applied to non-character
   * arguments.
   */
  static bool isConstRegExp(TNode t);
  /**
   * Does the substring of s occur in constant regular expression r?
   */
  static bool testConstStringInRegExp(String& s, TNode r);
  /** Does regular expression node have (str.to.re "") as a child? */
  static bool hasEpsilonNode(TNode node);
  /** get length for regular expression
   *
   * Given regular expression n, if this method returns a non-null value c, then
   * x in n entails len( x ) = c.
   */
  static Node getFixedLengthForRegexp(TNode n);

  /**
   * Get constant lower or upper bound on the lengths of strings that occur in
   * regular expression n. Return null if a constant bound cannot be determined.
   * This method will always worst case return 0 as a lower bound.
   */
  Node getConstantBoundLengthForRegexp(TNode n, bool isLower) const;
  /**
   * Returns true if we can show that the regular expression `r1` includes
   * the regular expression `r2` (i.e. `r1` matches a superset of sequences
   * that `r2` matches). This method only works on a fragment of regular
   * expressions, specifically regular expressions that pass the
   * `isSimpleRegExp` check.
   *
   * @param r1 The regular expression that may include `r2` (must be in
   *           rewritten form)
   * @param r2 The regular expression that may be included by `r1` (must be
   *           in rewritten form)
   * @return True if the inclusion can be shown, false otherwise
   */
  static bool regExpIncludes(Node r1,
                             Node r2,
                             std::map<std::pair<Node, Node>, bool>& cache);
  /** Same as above, without cache */
  static bool regExpIncludes(Node r1, Node r2);
 private:
  /**
   * Does the substring of s starting at index_start occur in constant regular
   * expression r?
   */
  static bool testConstStringInRegExpInternal(String& s,
                                              unsigned index_start,
                                              TNode r);
  /** Set bound cache, used for getConstantBoundLengthForRegexp */
  static void setConstantBoundCache(TNode n, Node ret, bool isLower);
  /**
   * Get bound cache, store in c and return true if the bound for n has been
   * computed. Used for getConstantBoundLengthForRegexp.
   */
  static bool getConstantBoundCache(TNode n, bool isLower, Node& c);
  /** Arithmetic entailment module */
  ArithEntail d_aent;
  /** Common constants */
  Node d_zero;
  Node d_one;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__REGEXP_ENTAIL_H */
