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
}; /* class SequencesRewriter */

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__SEQUENCES_REWRITER_H */
