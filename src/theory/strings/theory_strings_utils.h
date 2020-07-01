/*********************                                                        */
/*! \file theory_strings_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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
 * Returns (pre t n), which is (str.substr t 0 n).
 */
Node mkPrefix(Node t, Node n);

/**
 * Returns (suf t n), which is (str.substr t n (- (str.len t) n)).
 */
Node mkSuffix(Node t, Node n);

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
 * Return if a string-like term n is "constant-like", that is, either a
 * constant string/sequence, or an application of seq.unit.
 *
 * @param n The string-like term
 * @return true if n is constant-like.
 */
bool isConstantLike(Node n);

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
/** is k a native operator whose return type is a regular expression? */
bool isRegExpKind(Kind k);

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

}  // namespace utils
}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif
