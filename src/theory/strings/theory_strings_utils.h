/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Util functions for theory strings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__THEORY_STRINGS_UTILS_H
#define CVC5__THEORY__STRINGS__THEORY_STRINGS_UTILS_H

#include <vector>

#include "cvc5/cvc5_proof_rule.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

class SkolemCache;

namespace utils {

/** get the default cardinality of the alphabet used */
uint32_t getDefaultAlphabetCardinality();

/**
 * Make the conjunction of nodes in a. Removes duplicate conjuncts, returns
 * true if a is empty, and a single literal if a has size 1.
 */
Node mkAnd(NodeManager* nm, const std::vector<Node>& a);

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
 * when n = "", c is { "" }
 *
 * Also applies to regular expressions (re.++ above).
 */
void getConcat(Node n, std::vector<Node>& c);

/**
 * Make the concatenation from vector c of (string-like or regular
 * expression) type tn.
 */
Node mkConcat(const std::vector<Node>& c, TypeNode tn);

/**
 * Returns (pre t n), which is (str.substr t 0 n).
 */
Node mkPrefix(Node t, Node n);

/**
 * Returns (suf t n), which is (str.substr t n (- (str.len t) n)).
 */
Node mkSuffix(Node t, Node n);

/**
 * Returns (str.substr t 0 (- (str.len t) n)).
 */
Node mkPrefixExceptLen(Node t, Node n);
/**
 * Returns (str.substr t (- (str.len t) n) n).
 */
Node mkSuffixOfLen(Node t, Node n);

/**
 * Make a unit, returns either (str.unit n) or (seq.unit n) depending
 * on if tn is a string or a sequence.
 */
Node mkUnit(TypeNode tn, Node n);

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
 * Make the concatenation of seq.unit chains for a given constant sequence.
 */
Node mkConcatForConstSequence(const Node& c);

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
 * Return true if the arguments of REGEXP_RANGE term t are characters.
 */
bool isCharacterRange(TNode t);

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

/** Print the vector n as a concatenation term on output stream out */
void printConcat(std::ostream& out, std::vector<Node>& n);
/** Print the vector n as a concatenation term on trace given by c */
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

/**
 * Make internal quantified formula with bound variable list bvl and body.
 * Internally, we get a node corresponding to marking a quantified formula as
 * an "internal" one. This node is provided as the third argument of the
 * FORALL returned by this method. This ensures that E-matching is not applied
 * to the quantified formula.
 */
Node mkForallInternal(NodeManager* nm, Node bvl, Node body);

/**
 * Make abstract value for string-like term n whose length is given by len.
 * This is used for constructing models for strings whose lengths are too large
 * to represent in memory.
 */
Node mkAbstractStringValueForLength(Node n, Node len, size_t id);

/**
 * Make the formula (and (>= t 0) (< t alphaCard)).
 */
Node mkCodeRange(Node t, uint32_t alphaCard);

/** The eager reduce routine
 *
 * Constructs a lemma for t that is incomplete, but communicates pertinent
 * information about t. This is analogous to StringsPreprocess::reduce.
 *
 * In practice, we send this lemma eagerly, as soon as t is registered.
 *
 * @param t The node to reduce,
 * @param sc The Skolem cache to use for new variables,
 * @param alphaCard The cardinality of the alphabet we are assuming
 * @return The eager reduction for t.
 */
Node eagerReduce(Node t, SkolemCache* sc, uint32_t alphaCard);
/**
 * Returns a lemma indicating that the length of a term t whose type is
 * string-like has positive length. The exact form of this lemma depends
 * on what works best in practice, currently:
 *   (or (and (= (str.len t) 0) (= t "")) (> (str.len t) 0))
 *
 * @param t The node to reduce,
 * @return The positive length lemma for t.
 */
Node lengthPositive(Node t);
/**
 * This returns the conclusion of the proof rule corresponding to splitting
 * on the arrangement of terms x and y appearing in an equation of the form
 *   x ++ x' = y ++ y' or x' ++ x = y' ++ y
 * where we are in the second case if isRev is true. This method is called
 * both by the core solver and by the strings proof checker.
 *
 * @param nm Pointer to the node manager
 * @param x The first term
 * @param y The second term
 * @param rule The proof rule whose conclusion we are asking for
 * @param isRev Whether the equation is in a reverse direction
 * @param skc The skolem cache (to allocate fresh variables if necessary)
 * @param newSkolems The vector to add new variables to
 * @return The conclusion of the inference.
 */
Node getConcatConclusion(NodeManager* nm,
                         Node x,
                         Node y,
                         ProofRule rule,
                         bool isRev,
                         SkolemCache* skc,
                         std::vector<Node>& newSkolems);
/**
 * Get sufficient non-empty overlap of string constants c and d.
 *
 * This is called when handling equations of the form:
 *   x ++ d ++ ... = c ++ ...
 * when x is non-empty and non-constant.
 *
 * This returns the maximal index in c which x must have as a prefix, which
 * notice is an integer >= 1 since x is non-empty.
 *
 * @param c The first constant
 * @param d The second constant
 * @param isRev Whether the equation is in the reverse direction
 * @return The position in c.
 */
size_t getSufficientNonEmptyOverlap(Node c, Node d, bool isRev);
/**
 * This returns the conclusion of the decompose proof rule. This returns
 * a conjunction of splitting string x into pieces based on length l, e.g.:
 *   x = k_1 ++ k_2
 * where k_1 (resp. k_2) is a skolem corresponding to a substring of x of
 * length l if isRev is false (resp. true). The function also adds a
 * length constraint len(k_1) = l (resp. len(k_2) = l). Note that adding this
 * constraint to the conclusion is *not* optional, since the skolems k_1 and
 * k_2 may be shared, hence their length constraint must be guarded by the
 * premises of this inference.
 *
 * @param nm Pointer to the node manager
 * @param x The string term
 * @param l The length term
 * @param isRev Whether the equation is in a reverse direction
 * @param skc The skolem cache (to allocate fresh variables if necessary)
 * @param newSkolems The vector to add new variables to
 * @return The conclusion of the inference.
 */
Node getDecomposeConclusion(NodeManager* nm,
                            Node x,
                            Node l,
                            bool isRev,
                            SkolemCache* skc,
                            std::vector<Node>& newSkolems);
/**
 * This returns the conclusion of the extensionality rule, see
 * ProofRule::STRING_EXT.
 *
 * @param nm Pointer to the node manager
 * @param a The first string term
 * @param b The second string term
 * @param skc The skolem cache (to allocate fresh variables if necessary)
 * @return The conclusion of the inference.
 */
Node getExtensionalityConclusion(NodeManager* nm,
                                 const Node& a,
                                 const Node& b,
                                 SkolemCache* skc);

}  // namespace utils
}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif
