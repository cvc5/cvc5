/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for words.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__WORD_H
#define CVC5__THEORY__STRINGS__WORD_H

#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

// ------------------------------ for words (string or sequence constants)
class Word
{
 public:
  /** make empty constant of type tn */
  static Node mkEmptyWord(TypeNode tn);

  /** make word from constants in (non-empty) vector vec */
  static Node mkWordFlatten(const std::vector<Node>& xs);

  /** Return the length of word x */
  static size_t getLength(TNode x);

  /** Get characters
   *
   * Given word x, this returns the vector of words of length one whose
   * concatenation is equivalent to x.
   */
  static std::vector<Node> getChars(TNode x);
  /**
   * Get nth. If x is a string constant, this returns the constant integer
   * corresponding to the code point of x at position n. If x is a sequence
   * constant, then this returns the nth element of x.
   */
  static Node getNth(TNode x, size_t n);

  /** Return true if x is empty */
  static bool isEmpty(TNode x);

  /** string compare
   *
   * Returns true if x is equal to y for their first n characters.
   * If n is larger than the length of x or y, this method returns
   * true if and only if x is equal to y.
   */
  static bool strncmp(TNode x, TNode y, std::size_t n);

  /** reverse string compare
   *
   * Returns true if x is equal to y for their last n characters.
   * If n is larger than the length of tx or y, this method returns
   * true if and only if x is equal to y.
   */
  static bool rstrncmp(TNode x, TNode y, std::size_t n);

  /** Return the first position y occurs in x, or std::string::npos otherwise */
  static std::size_t find(TNode x, TNode y, std::size_t start = 0);

  /**
   * Return the first position y occurs in x searching from the end of x, or
   * std::string::npos otherwise
   */
  static std::size_t rfind(TNode x, TNode y, std::size_t start = 0);

  /** Returns true if y is a prefix of x */
  static bool hasPrefix(TNode x, TNode y);

  /** Returns true if y is a suffix of x */
  static bool hasSuffix(TNode x, TNode y);

  /** Replace the character at index n in x with t */
  static Node update(TNode x, std::size_t n, TNode t);

  /** Replace the first occurrence of y in x with t */
  static Node replace(TNode x, TNode y, TNode t);

  /** Return the substring/subsequence of x starting at index i */
  static Node substr(TNode x, std::size_t i);

  /** Return the substring/subsequence of x starting at index i with size at
   * most
   * j */
  static Node substr(TNode x, std::size_t i, std::size_t j);

  /** Return the prefix of x of size at most i */
  static Node prefix(TNode x, std::size_t i);

  /** Return the suffix of x of size at most i */
  static Node suffix(TNode x, std::size_t i);

  /**
   * Checks if there is any overlap between word x and another word y. This
   * corresponds to checking whether one string contains the other and whether a
   * substring/subsequence of one is a prefix of the other and/or vice-versa.
   *
   * If rev=false, this method returns true if x is non-empty, and either
   * x contains y, or a non-empty suffix of x is a prefix of y.
   * Examples:
   *   "", "" -> false
   *   "", "a" -> false
   *   "abc", "" -> true
   *   "abc", "aa" -> false
   *   "abc", "cd" -> true
   *   "abc", "b" -> true
   *   "abc", "abcd" -> true
   *   "abc", "aab" -> false
   *
   * Overall, the intuition is the following when rev=false:
   *   If hasOverlap(c, d, false) returns false, then the first occurence (if any)
   *   of d in a string of the form c++e is as a substring of e, for any e.
   *   In other words, the content of c does not contribute to where d is contained
   *   when looking from the start of the string.
   *
   * If rev=true, this method returns true if x is non-empty, and either
   * x contains y, or a non-empty prefix of x is a suffix of y.
   * Examples:
   *   "", "" -> false
   *   "", "a" -> false
   *   "abc", "" -> true
   *   "abc", "aa" -> true
   *   "abc", "cd" -> false
   *   "abc", "b" -> true
   *   "abc", "abcd" -> false
   *   "abc", "aab" -> true
   *
   * Overall, the intuition of this operation is the following when rev=true:
   *   If hasOverlap(c, d, true) returns false, then the last occurence (if any)
   *   of d in a string of the form e++c is as a substring of e, for any e.
   *   In other words, the content of c does not contribute to where d is contained
   *   when looking from the end of the string.
   *
   * @param x The first string
   * @param y The second string
   * @param rev Whether we are checking the reverse direction.
   * @return True if there is an overlap, false otherwise
   */
  static bool hasOverlap(TNode x, TNode y, bool rev);
  /**
   * Equivalent to hasOverlap(x, y, false) || hasOverlap(y, x, false).
   */
  static bool hasBidirectionalOverlap(TNode x, TNode y);

  /** overlap
   *
   * when overlap returns m,
   * then the maximal suffix of this string that is a prefix of y is of length
   * m.
   *
   * For example, if x is "abcdef", then:
   * x.overlap("defg") = 3
   * x.overlap("ab") = 0
   * x.overlap("d") = 0
   * x.overlap("bcdefdef") = 5
   */
  static std::size_t overlap(TNode x, TNode y);

  /** reverse overlap
   *
   * when roverlap returns m,
   * then the maximal prefix of this word that is a suffix of y is of length m.
   *
   * For example, if x is "abcdef", then:
   * x.roverlap("aaabc") = 3
   * x.roverlap("def") = 0
   * x.roverlap("d") = 0
   * x.roverlap("defabcde") = 5
   *
   * Notice that x.overlap(y) = y.roverlap(x)
   */
  static std::size_t roverlap(TNode x, TNode y);
  /** Return true if word x is a repetition of the same character */
  static bool isRepeated(TNode x);
  /** Split constant
   *
   * This returns the suffix remainder (resp. prefix remainder when isRev is
   * true) of words a and b, call it r, such that:
   * (1) a = b ++ r , or
   * (2) a ++ r = b
   * when isRev = false.  The argument index is set to 1 if we are in the second
   * case, and 0 otherwise.
   *
   * If a and b do not share a common prefix (resp. suffix), then this method
   * returns the null node.
   */
  static Node splitConstant(TNode x, TNode y, size_t& index, bool isRev);
  /** reverse
   *
   * Return the result of reversing x.
   */
  static Node reverse(TNode x);
};

// ------------------------------ end for words (string or sequence constants)

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif
