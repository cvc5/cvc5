/*********************                                                        */
/*! \file word.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility functions for words.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__WORD_H
#define CVC4__THEORY__STRINGS__WORD_H

#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace strings {
namespace word {

// ------------------------------ for words (string or sequence constants)

/** make empty constant of kind k */
Node mkEmptyWord(Kind k);

/** make word from constants in vector vec */
Node mkWord(const std::vector<Node>& xs);

/** Return the length of word x */
size_t getLength(TNode x);

/** Return true if x is empty */
bool isEmpty(TNode x);

/** Return the first position y occurs in x, or std::string::npos otherwise */
std::size_t find(TNode x, TNode y, std::size_t start = 0);

/**
 * Return the first position y occurs in x searching from the end of x, or
 * std::string::npos otherwise
 */
std::size_t rfind(TNode x, TNode y, std::size_t start = 0);

/** Returns true if y is a prefix of x */
bool hasPrefix(TNode x, TNode y);

/** Returns true if y is a suffix of x */
bool hasSuffix(TNode x, TNode y);

/** Replace the first occurrence of y in x with t */
Node replace(TNode x, TNode y, TNode t);

/** Return the substring of x starting at index i */
Node substr(TNode x, std::size_t i);

/** Return the substring of x starting at index i with size at most j */
Node substr(TNode x, std::size_t i, std::size_t j);

/** Return the prefix of x of size at most i */
Node prefix(TNode x, std::size_t i);

/** Return the suffix of x of size at most i */
Node suffix(TNode x, std::size_t i);

/**
 * Checks if there is any overlap between string x and another string y. This
 * corresponds to checking whether one string contains the other and whether a
 * substring of one is a prefix of the other and vice-versa.
 *
 * @param x The first string
 * @param y The second string
 * @return True if there is an overlap, false otherwise
 */
bool noOverlapWith(TNode x, TNode y);

/** overlap
 *
 * if overlap returns m>0,
 * then the maximal suffix of this string that is a prefix of y is of length m.
 *
 * For example, if x is "abcdef", then:
 * x.overlap("defg") = 3
 * x.overlap("ab") = 0
 * x.overlap("d") = 0
 * x.overlap("bcdefdef") = 5
 */
std::size_t overlap(TNode x, TNode y);

/** reverse overlap
 *
 * if roverlap returns m>0,
 * then the maximal prefix of this string that is a suffix of y is of length m.
 *
 * For example, if x is "abcdef", then:
 * x.roverlap("aaabc") = 3
 * x.roverlap("def") = 0
 * x.roverlap("d") = 0
 * x.roverlap("defabcde") = 5
 *
 * Notice that x.overlap(y) = y.roverlap(x)
 */
std::size_t roverlap(TNode x, TNode y);

// ------------------------------ end for words (string or sequence constants)

}  // namespace word
}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif
