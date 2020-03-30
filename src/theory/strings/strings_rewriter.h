/*********************                                                        */
/*! \file strings_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewrite rules for string-specific operators in theory of strings
 **
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__STRINGS_REWRITER_H
#define CVC4__THEORY__STRINGS__STRINGS_REWRITER_H

#include "expr/node.h"
#include "theory/strings/sequences_rewriter.h"

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * An extension of SequencesRewriter that handles operators that
 * are specific to strings (and cannot be applied to sequences).
 */
class StringsRewriter : public SequencesRewriter
{
 public:
  /** rewrite string to integer
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.to_int( s )
   * Returns the rewritten form of n.
   */
  static Node rewriteStrToInt(Node n);

  /** rewrite integer to string
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.from_int( i )
   * Returns the rewritten form of n.
   */
  static Node rewriteIntToStr(Node n);

  /** rewrite string convert
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.tolower( s ) and str.toupper( s )
   * Returns the rewritten form of n.
   */
  static Node rewriteStrConvert(Node n);

  /** rewrite string less than
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.<( t, s )
   * Returns the rewritten form of n.
   */
  static Node rewriteStringLt(Node n);

  /** rewrite string less than or equal
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.<=( t, s )
   * Returns the rewritten form of n.
   */
  static Node rewriteStringLeq(Node n);

  /** rewrite str.from_code
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.from_code( t )
   * Returns the rewritten form of n.
   */
  static Node rewriteStringFromCode(Node n);

  /** rewrite str.to_code
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.to_code( t )
   * Returns the rewritten form of n.
   */
  static Node rewriteStringToCode(Node n);

  /** rewrite is digit
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.is_digit( t )
   * Returns the rewritten form of n.
   */
  static Node rewriteStringIsDigit(Node n);
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__STRINGS_REWRITER_H */
