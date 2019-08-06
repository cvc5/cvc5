/*********************                                                        */
/*! \file theory_strings_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewriter for the theory of strings
 **
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__THEORY_STRINGS_REWRITER_H
#define CVC4__THEORY__STRINGS__THEORY_STRINGS_REWRITER_H

#include <utility>
#include <vector>

#include "theory/rewriter.h"
#include "theory/type_enumerator.h"
#include "expr/attribute.h"
#include <climits>

namespace CVC4 {
namespace theory {
namespace strings {

class TheoryStringsRewriter {
 private:
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
  static Node simpleRegexpConsume( std::vector< Node >& mchildren, std::vector< Node >& children, int dir = -1 );
  static bool isConstRegExp( TNode t );
  static bool testConstStringInRegExp( CVC4::String &s, unsigned int index_start, TNode r );

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
  /** rewrite regular expression membership
   *
   * This is the entry point for post-rewriting applications of str.in.re
   * Returns the rewritten form of node.
   */
  static Node rewriteMembership(TNode node);

  static bool hasEpsilonNode(TNode node);
  /** check entail arithmetic internal
   * Returns true if we can show a >= 0 always.
   * a is in rewritten form.
   */
  static bool checkEntailArithInternal(Node a);
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
   * The string c indicates the justification for the rewrite, which is printed
   * by this function for debugging.
   *
   * If node is not an equality and ret is an equality, this method applies
   * an additional rewrite step (rewriteEqualityExt) that performs
   * additional rewrites on ret, after which we return the result of this call.
   * Otherwise, this method simply returns ret.
   */
  static Node returnRewrite(Node node, Node ret, const char* c);

 public:
  static RewriteResponse postRewrite(TNode node);
  static RewriteResponse preRewrite(TNode node);

  static inline void init() {}
  static inline void shutdown() {}
  /** get the cardinality of the alphabet used, based on the options */
  static unsigned getAlphabetCardinality();
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
  /** rewrite concat
  * This is the entry point for post-rewriting terms node of the form
  *   str.++( t1, .., tn )
  * Returns the rewritten form of node.
  */
  static Node rewriteConcat(Node node);
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
  /** rewrite string convert
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.tolower( s ) and str.toupper( s )
   * Returns the rewritten form of node.
   */
  static Node rewriteStrConvert(Node node);
  /** rewrite string less than or equal
  * This is the entry point for post-rewriting terms n of the form
  *   str.<=( t, s )
  * Returns the rewritten form of n.
  */
  static Node rewriteStringLeq(Node n);
  /** rewrite prefix/suffix
  * This is the entry point for post-rewriting terms n of the form
  *   str.prefixof( s, t ) / str.suffixof( s, t )
  * Returns the rewritten form of node.
  */
  static Node rewritePrefixSuffix(Node node);
  /** rewrite str.code
   * This is the entry point for post-rewriting terms n of the form
   *   str.code( t )
   * Returns the rewritten form of node.
   */
  static Node rewriteStringCode(Node node);

  static Node splitConstant( Node a, Node b, int& index, bool isRev );
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
  static bool canConstantContainList( Node c, std::vector< Node >& l, int& firstc, int& lastc );
  /** can constant contain concat
  * same as above but with n = str.++( l ) instead of l
  */
  static bool canConstantContainConcat(Node c, Node n, int& firstc, int& lastc);
  static Node getNextConstantAt( std::vector< Node >& vec, unsigned& start_index, unsigned& end_index, bool isRev );
  static Node collectConstantStringAt( std::vector< Node >& vec, unsigned& end_index, bool isRev );

  /** strip symbolic length
   *
   * This function strips off components of n1 whose length is less than
   * or equal to argument curr, and stores them in nr. The direction
   * dir determines whether the components are removed from the start
   * or end of n1.
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
  static bool stripSymbolicLength(std::vector<Node>& n1,
                                  std::vector<Node>& nr,
                                  int dir,
                                  Node& curr);
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
  */
  static int componentContains(std::vector<Node>& n1,
                               std::vector<Node>& n2,
                               std::vector<Node>& nb,
                               std::vector<Node>& ne,
                               bool computeRemainder = false,
                               int remainderDir = 0);
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
   * Since we do not wish to introduce ITE terms in the rewriter, we instead
   * return false, indicating that we cannot compute the remainder.
   */
  static bool componentContainsBase(
      Node n1, Node n2, Node& n1rb, Node& n1re, int dir, bool computeRemainder);
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
   * Given a symbolic length n, returns the canonical string for that length.
   * For example if n is constant, this function returns a string consisting of
   * "A" repeated n times. Returns the null node if no such string exists.
   */
  static Node canonicalStrForSymbolicLength(Node n);

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

  /** check arithmetic entailment equal
   * Returns true if it is always the case that a = b.
   */
  static bool checkEntailArithEq(Node a, Node b);
  /** check arithmetic entailment
   * Returns true if it is always the case that a >= b,
   * and a>b if strict is true.
   */
  static bool checkEntailArith(Node a, Node b, bool strict = false);
  /** check arithmetic entailment
   * Returns true if it is always the case that a >= 0.
   */
  static bool checkEntailArith(Node a, bool strict = false);
  /** check arithmetic entailment with approximations
   *
   * Returns true if it is always the case that a >= 0. We expect that a is in
   * rewritten form.
   *
   * This function uses "approximation" techniques that under-approximate
   * the value of a for the purposes of showing the entailment holds. For
   * example, given:
   *   len( x ) - len( substr( y, 0, len( x ) ) )
   * Since we know that len( substr( y, 0, len( x ) ) ) <= len( x ), the above
   * term can be under-approximated as len( x ) - len( x ) = 0, which is >= 0,
   * and thus the entailment len( x ) - len( substr( y, 0, len( x ) ) ) >= 0
   * holds.
   */
  static bool checkEntailArithApprox(Node a);
  /** Get arithmetic approximations
   *
   * This gets the (set of) arithmetic approximations for term a and stores
   * them in approx. If isOverApprox is true, these are over-approximations
   * for the value of a, otherwise, they are underapproximations. For example,
   * an over-approximation for len( substr( y, n, m ) ) is m; an
   * under-approximation for indexof( x, y, n ) is -1.
   *
   * Notice that this function is not generally recursive (although it may make
   * a small bounded of recursive calls). Instead, it returns the shape
   * of the approximations for a. For example, an under-approximation
   * for the term len( replace( substr( x, 0, n ), y, z ) ) returned by this
   * function might be len( substr( x, 0, n ) ) - len( y ), where we don't
   * consider (recursively) the approximations for len( substr( x, 0, n ) ).
   */
  static void getArithApproximations(Node a,
                                     std::vector<Node>& approx,
                                     bool isOverApprox = false);

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
   * Checks whether assumption |= a >= 0 (if strict is false) or
   * assumption |= a > 0 (if strict is true), where assumption is an equality
   * assumption. The assumption must be in rewritten form.
   *
   * Example:
   *
   * checkEntailArithWithEqAssumption(x + (str.len y) = 0, -x, false) = true
   *
   * Because: x = -(str.len y), so -x >= 0 --> (str.len y) >= 0 --> true
   */
  static bool checkEntailArithWithEqAssumption(Node assumption,
                                               Node a,
                                               bool strict = false);

  /**
   * Checks whether assumption |= a >= b (if strict is false) or
   * assumption |= a > b (if strict is true). The function returns true if it
   * can be shown that the entailment holds and false otherwise. Assumption
   * must be in rewritten form. Assumption may be an equality or an inequality.
   *
   * Example:
   *
   * checkEntailArithWithAssumption(x + (str.len y) = 0, 0, x, false) = true
   *
   * Because: x = -(str.len y), so 0 >= x --> 0 >= -(str.len y) --> true
   */
  static bool checkEntailArithWithAssumption(Node assumption,
                                             Node a,
                                             Node b,
                                             bool strict = false);

  /**
   * Checks whether assumptions |= a >= b (if strict is false) or
   * assumptions |= a > b (if strict is true). The function returns true if it
   * can be shown that the entailment holds and false otherwise. Assumptions
   * must be in rewritten form. Assumptions may be an equalities or an
   * inequalities.
   *
   * Example:
   *
   * checkEntailArithWithAssumptions([x + (str.len y) = 0], 0, x, false) = true
   *
   * Because: x = -(str.len y), so 0 >= x --> 0 >= -(str.len y) --> true
   */
  static bool checkEntailArithWithAssumptions(std::vector<Node> assumptions,
                                              Node a,
                                              Node b,
                                              bool strict = false);

  /** get arithmetic lower bound
   * If this function returns a non-null Node ret,
   * then ret is a rational constant and
   * we know that n >= ret always if isLower is true,
   * or n <= ret if isLower is false.
   *
   * Notice the following invariant.
   * If getConstantArithBound(a, true) = ret where ret is non-null, then for
   * strict = { true, false } :
   *   ret >= strict ? 1 : 0
   *     if and only if
   *   checkEntailArith( a, strict ) = true.
   */
  static Node getConstantArithBound(Node a, bool isLower = true);
  /** get length for regular expression
   *
   * Given regular expression n, if this method returns a non-null value c, then
   * x in n entails len( x ) = c.
   */
  static Node getFixedLengthForRegexp(Node n);
  /** decompose substr chain
   *
   * If s is substr( ... substr( base, x1, y1 ) ..., xn, yn ), then this
   * function returns base, adds { x1 ... xn } to ss, and { y1 ... yn } to ls.
   */
  static Node decomposeSubstrChain(Node s,
                                   std::vector<Node>& ss,
                                   std::vector<Node>& ls);
  /** make substr chain
   *
   * If ss is { x1 ... xn } and ls is { y1 ... yn }, this returns the term
   * substr( ... substr( base, x1, y1 ) ..., xn, yn ).
   */
  static Node mkSubstrChain(Node base,
                            const std::vector<Node>& ss,
                            const std::vector<Node>& ls);

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
   * Given an inequality y1 + ... + yn >= x, removes operands yi s.t. the
   * original inequality still holds. Returns true if the original inequality
   * holds and false otherwise. The list of ys is modified to contain a subset
   * of the original ys.
   *
   * Example:
   *
   * inferZerosInSumGeq( (str.len x), [ (str.len x), (str.len y), 1 ], [] )
   * --> returns true with ys = [ (str.len x) ] and zeroYs = [ (str.len y), 1 ]
   *     (can be used to rewrite the inequality to false)
   *
   * inferZerosInSumGeq( (str.len x), [ (str.len y) ], [] )
   * --> returns false because it is not possible to show
   *     str.len(y) >= str.len(x)
   */
  static bool inferZerosInSumGeq(Node x,
                                 std::vector<Node>& ys,
                                 std::vector<Node>& zeroYs);

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
};/* class TheoryStringsRewriter */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__THEORY_STRINGS_REWRITER_H */
