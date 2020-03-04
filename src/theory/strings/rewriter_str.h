/*********************                                                        */
/*! \file rewriter_str.h
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

#ifndef CVC4__THEORY__STRINGS__REWRITER_STR_H
#define CVC4__THEORY__STRINGS__REWRITER_STR_H

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace strings {

class RewriterStr
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
private:
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
}; /* class TheoryStringsRewriter */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__REWRITER_STR_H */
