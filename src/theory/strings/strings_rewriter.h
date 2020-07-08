/*********************                                                        */
/*! \file strings_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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
  StringsRewriter(HistogramStat<Rewrite>* statistics);

  RewriteResponse postRewrite(TNode node) override;

  /** rewrite string to integer
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.to_int( s )
   * Returns the rewritten form of n.
   */
  Node rewriteStrToInt(Node n);

  /** rewrite integer to string
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.from_int( i )
   * Returns the rewritten form of n.
   */
  Node rewriteIntToStr(Node n);

  /** rewrite string convert
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.tolower( s ) and str.toupper( s )
   * Returns the rewritten form of n.
   */
  Node rewriteStrConvert(Node n);

  /** rewrite string less than
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.<( t, s )
   * Returns the rewritten form of n.
   */
  Node rewriteStringLt(Node n);

  /** rewrite string less than or equal
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.<=( t, s )
   * Returns the rewritten form of n.
   */
  Node rewriteStringLeq(Node n);

  /** rewrite str.from_code
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.from_code( t )
   * Returns the rewritten form of n.
   */
  Node rewriteStringFromCode(Node n);

  /** rewrite str.to_code
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.to_code( t )
   * Returns the rewritten form of n.
   */
  Node rewriteStringToCode(Node n);

  /** rewrite is digit
   *
   * This is the entry point for post-rewriting terms n of the form
   *   str.is_digit( t )
   * Returns the rewritten form of n.
   */
  Node rewriteStringIsDigit(Node n);
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__STRINGS_REWRITER_H */
