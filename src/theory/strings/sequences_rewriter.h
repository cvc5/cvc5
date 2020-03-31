/*********************                                                        */
/*! \file sequences_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewriter for the theory of strings and sequences
 **
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__SEQUENCES_REWRITER_H
#define CVC4__THEORY__STRINGS__SEQUENCES_REWRITER_H

#include <climits>
#include <utility>
#include <vector>

#include "expr/attribute.h"
#include "theory/strings/rewrites.h"
#include "theory/theory_rewriter.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace strings {

class SequencesRewriter : public TheoryRewriter
{
 protected:
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
  static bool isConstRegExp(TNode t);
  static bool testConstStringInRegExp(CVC4::String& s,
                                      unsigned int index_start,
                                      TNode r);

  /** rewrite regular expression concatenation
   *
   * This is the entry point for post-rewriting applications of re.++.
   * Returns the rewritten form of node.
   */
  static Node rewriteConcatRegExp(TNode node);
  /** rewrite regular expression star
   *
   * This is the entry point for post-rewriting applications of re.*.
   * Returns the rewritten form of node.
   */
  static Node rewriteStarRegExp(TNode node);
  /** rewrite regular expression intersection/union
   *
   * This is the entry point for post-rewriting applications of re.inter and
   * re.union. Returns the rewritten form of node.
   */
  static Node rewriteAndOrRegExp(TNode node);
  /** rewrite regular expression loop
   *
   * This is the entry point for post-rewriting applications of re.loop.
   * Returns the rewritten form of node.
   */
  static Node rewriteLoopRegExp(TNode node);
  /** rewrite regular expression repeat
   *
   * This is the entry point for post-rewriting applications of re.repeat.
   * Returns the rewritten form of node.
   */
  static Node rewriteRepeatRegExp(TNode node);
  /** rewrite regular expression option
   *
   * This is the entry point for post-rewriting applications of re.opt.
   * Returns the rewritten form of node.
   */
  static Node rewriteOptionRegExp(TNode node);
  /** rewrite regular expression plus
   *
   * This is the entry point for post-rewriting applications of re.+.
   * Returns the rewritten form of node.
   */
  static Node rewritePlusRegExp(TNode node);
  /** rewrite regular expression difference
   *
   * This is the entry point for post-rewriting applications of re.diff.
   * Returns the rewritten form of node.
   */
  static Node rewriteDifferenceRegExp(TNode node);
  /** rewrite regular expression range
   *
   * This is the entry point for post-rewriting applications of re.range.
   * Returns the rewritten form of node.
   */
  static Node rewriteRangeRegExp(TNode node);

  /** rewrite regular expression membership
   *
   * This is the entry point for post-rewriting applications of str.in.re
   * Returns the rewritten form of node.
   */
  static Node rewriteMembership(TNode node);

  static bool hasEpsilonNode(TNode node);
  /** rewrite string equality extended
   *
   * This method returns a formula that is equivalent to the equality between
   * two strings s = t, given by node. It is called by rewriteEqualityExt.
   */
  static Node rewriteStrEqualityExt(Node node);
  /** rewrite arithmetic equality extended
   *
   * This method returns a formula that is equivalent to the equality between
   * two arithmetic string terms s = t, given by node. t is called by
   * rewriteEqualityExt.
   */
  static Node rewriteArithEqualityExt(Node node);
  /**
   * Called when node rewrites to ret.
   *
   * The rewrite r indicates the justification for the rewrite, which is printed
   * by this function for debugging.
   *
   * If node is not an equality and ret is an equality, this method applies
   * an additional rewrite step (rewriteEqualityExt) that performs
   * additional rewrites on ret, after which we return the result of this call.
   * Otherwise, this method simply returns ret.
   */
  static Node returnRewrite(Node node, Node ret, Rewrite r);

 public:
  RewriteResponse postRewrite(TNode node) override;
  RewriteResponse preRewrite(TNode node) override;

  /** rewrite equality
   *
   * This method returns a formula that is equivalent to the equality between
   * two strings s = t, given by node. The result of rewrite is one of
   * { s = t, t = s, true, false }.
   */
  static Node rewriteEquality(Node node);
  /** rewrite equality extended
   *
   * This method returns a formula that is equivalent to the equality between
   * two terms s = t, given by node, where s and t are terms in the signature
   * of the theory of strings. Notice that s and t may be of string type or
   * of Int type.
   *
   * Specifically, this function performs rewrites whose conclusion is not
   * necessarily one of { s = t, t = s, true, false }.
   */
  static Node rewriteEqualityExt(Node node);
  /** rewrite string length
   * This is the entry point for post-rewriting terms node of the form
   *   str.len( t )
   * Returns the rewritten form of node.
   */
  static Node rewriteLength(Node node);
  /** rewrite concat
   * This is the entry point for post-rewriting terms node of the form
   *   str.++( t1, .., tn )
   * Returns the rewritten form of node.
   */
  static Node rewriteConcat(Node node);
  /** rewrite character at
   * This is the entry point for post-rewriting terms node of the form
   *   str.charat( s, i1 )
   * Returns the rewritten form of node.
   */
  static Node rewriteCharAt(Node node);
  /** rewrite substr
   * This is the entry point for post-rewriting terms node of the form
   *   str.substr( s, i1, i2 )
   * Returns the rewritten form of node.
   */
  static Node rewriteSubstr(Node node);
  /** rewrite contains
   * This is the entry point for post-rewriting terms node of the form
   *   str.contains( t, s )
   * Returns the rewritten form of node.
   *
   * For details on some of the basic rewrites done in this function, see Figure
   * 7 of Reynolds et al "Scaling Up DPLL(T) String Solvers Using
   * Context-Dependent Rewriting", CAV 2017.
   */
  static Node rewriteContains(Node node);
  /** rewrite indexof
   * This is the entry point for post-rewriting terms n of the form
   *   str.indexof( s, t, n )
   * Returns the rewritten form of node.
   */
  static Node rewriteIndexof(Node node);
  /** rewrite replace
   * This is the entry point for post-rewriting terms n of the form
   *   str.replace( s, t, r )
   * Returns the rewritten form of node.
   */
  static Node rewriteReplace(Node node);
  /** rewrite replace all
   * This is the entry point for post-rewriting terms n of the form
   *   str.replaceall( s, t, r )
   * Returns the rewritten form of node.
   */
  static Node rewriteReplaceAll(Node node);
  /** rewrite replace internal
   *
   * This method implements rewrite rules that apply to both str.replace and
   * str.replaceall. If it returns a non-null ret, then node rewrites to ret.
   */
  static Node rewriteReplaceInternal(Node node);
  /** rewrite string reverse
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.rev( s )
   * Returns the rewritten form of node.
   */
  static Node rewriteStrReverse(Node node);
  /** rewrite prefix/suffix
   * This is the entry point for post-rewriting terms n of the form
   *   str.prefixof( s, t ) / str.suffixof( s, t )
   * Returns the rewritten form of node.
   */
  static Node rewritePrefixSuffix(Node node);

  /** rewrite str.to_code
   * This is the entry point for post-rewriting terms n of the form
   *   str.to_code( t )
   * Returns the rewritten form of node.
   */
  static Node rewriteStringToCode(Node node);

  /** length preserving rewrite
   *
   * Given input n, this returns a string n' whose length is equivalent to n.
   * We apply certain normalizations to n', such as replacing all constants
   * that are not relevant to length by "A".
   */
  static Node lengthPreserveRewrite(Node n);

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
  static Node checkEntailContains(Node a, Node b, bool fullRewriter = true);

  /** entail non-empty
   *
   * Checks whether string a is entailed to be non-empty. Is equivalent to
   * the call checkArithEntail( len( a ), true ).
   */
  static bool checkEntailNonEmpty(Node a);

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
  static bool checkEntailLengthOne(Node s, bool strict = false);

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
  static bool checkEntailMultisetSubset(Node a, Node b);

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
  static Node checkEntailHomogeneousString(Node a);

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

  /**
   * Collects equal-to-empty nodes from a conjunction or a single
   * node. Returns a list of nodes that are compared to empty nodes
   * and a boolean that indicates whether all nodes in the
   * conjunction were a comparison with the empty node. The nodes in
   * the list are sorted and duplicates removed.
   *
   * Examples:
   *
   * collectEmptyEqs( (= "" x) ) = { true, [x] }
   * collectEmptyEqs( (and (= "" x) (= "" y)) ) = { true, [x, y] }
   * collectEmptyEqs( (and (= "A" x) (= "" y) (= "" y)) ) = { false, [y] }
   *
   * @param x The conjunction of equalities or a single equality
   * @return A pair of a boolean that indicates whether the
   * conjunction consists only of comparisons to the empty string
   * and the list of nodes that are compared to the empty string
   */
  static std::pair<bool, std::vector<Node> > collectEmptyEqs(Node x);
}; /* class SequencesRewriter */

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__SEQUENCES_REWRITER_H */
