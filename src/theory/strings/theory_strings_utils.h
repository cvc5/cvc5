/*********************                                                        */
/*! \file theory_strings_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Util functions for theory strings.
 **
 ** Util functions for theory strings.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__THEORY_STRINGS_UTILS_H
#define CVC4__THEORY__STRINGS__THEORY_STRINGS_UTILS_H

#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace strings {
namespace utils {

/** get the cardinality of the alphabet used, based on the options */
uint32_t getAlphabetCardinality();

/**
 * Make the conjunction of nodes in a. Removes duplicate conjuncts, returns
 * true if a is empty, and a single literal if a has size 1.
 */
Node mkAnd(const std::vector<Node>& a);

/**
 * Adds all (non-duplicate) children of <k> applications from n to conj. For
 * example, given (<k> (<k> A B) C A), we add { A, B, C } to conj.
 */
void flattenOp(Kind k, Node n, std::vector<Node>& conj);

/**
 * Gets the "vector form" of term n, adds it to c.
 *
 * For example:
 * when n = str.++( x, y ), c is { x, y }
 * when n = str.++( x, str.++( y, z ), w ), c is { x, str.++( y, z ), w )
 * when n = x, c is { x }
 *
 * Also applies to regular expressions (re.++ above).
 */
void getConcat(Node n, std::vector<Node>& c);

/**
 * Make the concatentation from vector c of (string-like or regular
 * expression) type tn.
 */
Node mkConcat(const std::vector<Node>& c, TypeNode tn);

/**
 * Returns the rewritten form of the string concatenation of n1 and n2.
 */
Node mkNConcat(Node n1, Node n2);

/**
 * Returns the rewritten form of the string concatenation of n1, n2 and n3.
 */
Node mkNConcat(Node n1, Node n2, Node n3);

/**
 * Returns the rewritten form of the concatentation from vector c of
 * (string-like) type tn.
 */
Node mkNConcat(const std::vector<Node>& c, TypeNode tn);

/**
 * Returns the rewritten form of the length of string term t.
 */
Node mkNLength(Node t);

/**
 * Get constant component. Returns the string constant represented by the
 * string or regular expression t. For example:
 *   "ABC" -> "ABC", (str.to.re "ABC") -> "ABC", (str.++ x "ABC") -> null
 */
Node getConstantComponent(Node t);

/**
 * Get constant prefix / suffix from expression. For example, if isSuf=false:
 *   "ABC" -> "ABC"
 *   (str.++ "ABC" x) -> "ABC"
 *   (str.to.re "ABC") -> "ABC"
 *   (re.++ (str.to.re "ABC") ...) -> "ABC"
 *   (re.in x (str.to.re "ABC")) -> "ABC"
 *   (re.in x (re.++ (str.to.re "ABC") ...)) -> "ABC"
 *   (str.++ x "ABC") -> null
 *   (re.in x (re.++ (re.* "D") (str.to.re "ABC"))) -> null
 */
Node getConstantEndpoint(Node e, bool isSuf);

/** decompose substr chain
 *
 * If s is substr( ... substr( base, x1, y1 ) ..., xn, yn ), then this
 * function returns base, adds { x1 ... xn } to ss, and { y1 ... yn } to ls.
 */
Node decomposeSubstrChain(Node s, std::vector<Node>& ss, std::vector<Node>& ls);
/** make substr chain
 *
 * If ss is { x1 ... xn } and ls is { y1 ... yn }, this returns the term
 * substr( ... substr( base, x1, y1 ) ..., xn, yn ).
 */
Node mkSubstrChain(Node base,
                   const std::vector<Node>& ss,
                   const std::vector<Node>& ls);

/** Split constant
 *
 * FIXME
 */
Node splitConstant(Node a, Node b, int& index, bool isRev);

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
bool canConstantContainList(Node c,
                            std::vector<Node>& l,
                            int& firstc,
                            int& lastc);
/** can constant contain concat
 * same as above but with n = str.++( l ) instead of l
 */
bool canConstantContainConcat(Node c, Node n, int& firstc, int& lastc);

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
bool stripSymbolicLength(std::vector<Node>& n1,
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
int componentContains(std::vector<Node>& n1,
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
bool componentContainsBase(
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
bool stripConstantEndpoints(std::vector<Node>& n1,
                            std::vector<Node>& n2,
                            std::vector<Node>& nb,
                            std::vector<Node>& ne,
                            int dir = 0);

/**
 * Given a symbolic length n, returns the canonical string (of type stype)
 * for that length. For example if n is constant, this function returns a
 * string consisting of "A" repeated n times. Returns the null node if no such
 * string exists.
 */
Node canonicalStrForSymbolicLength(Node n, TypeNode stype);

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
std::pair<bool, std::vector<Node> > collectEmptyEqs(Node x);

/**
 * Given a vector of regular expression nodes and a start index that points to
 * a wildcard, returns true if the wildcard is unbounded (i.e. it is followed
 * by an arbitrary number of `re.allchar`s and then an `re.*(re.allchar)`. If
 * the start index is not a wilcard or the wildcards are not followed by
 * `re.*(re.allchar)`, the function returns false.
 *
 * @param rs The vector of regular expression nodes
 * @param start The start index to consider
 * @return True if the wilcard pointed to by `start` is unbounded, false
 *         otherwise
 */
bool isUnboundedWildcard(const std::vector<Node>& rs, size_t start);

/**
 * Returns true iff the given regular expression only consists of re.++,
 * re.allchar, (re.* re.allchar), and str.to.re of string literals.
 *
 * @param r The regular expression to check
 * @return True if the regular expression is simple
 */
bool isSimpleRegExp(Node r);

/**
 * Helper function that takes a regular expression concatenation and
 * returns the components of the concatenation. Letters of string literals
 * are treated as individual components.
 *
 * @param r The regular expression
 * @param result The resulting components
 */
void getRegexpComponents(Node r, std::vector<Node>& result);

/** Print the vector n as a concatentation term on output stream out */
void printConcat(std::ostream& out, std::vector<Node>& n);
/** Print the vector n as a concatentation term on trace given by c */
void printConcatTrace(std::vector<Node>& n, const char* c);

/** Is k a string-specific kind? */
bool isStringKind(Kind k);

/** Get owner string type
 *
 * This returns a string-like type for a term n that belongs to the theory of
 * strings. This type conceptually represents the subtheory of strings
 * (Sequence(T) or String) that owns n. This is typically the type of n,
 * but for instance, operators like str.indexof( s, t, n ), this is the type
 * of s.
 */
TypeNode getOwnerStringType(Node n);

/* Get the number of repetitions for a regexp repeat node */
unsigned getRepeatAmount(TNode node);

/* Get the maximum occurrences of given regexp loop node. */
unsigned getLoopMaxOccurrences(TNode node);
/* Get the minimum occurrences of given regexp loop node. */
unsigned getLoopMinOccurrences(TNode node);

/** get length for regular expression
 *
 * Given regular expression n, if this method returns a non-null value c, then
 * x in n entails len( x ) = c.
 */
Node getFixedLengthForRegexp(Node n);

}  // namespace utils
}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif
