/*********************                                                        */
/*! \file expr_stream.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A stream interface for expressions
 **
 ** A stream interface for expressions.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__EXPR_STREAM_H
#define __CVC4__EXPR_STREAM_H

#include "expr/expr.h"

namespace CVC4 {

/**
 * A pure-virtual stream interface for expressions.  Can be used to
 * communicate streams of expressions between different parts of CVC4.
 */
class CVC4_PUBLIC ExprStream {
public:
  /** Virtual destructor; this implementation does nothing. */
  virtual ~ExprStream() {}

  /**
   * Get the next expression in the stream (advancing the stream
   * pointer as a side effect.)
   */
  virtual Expr nextExpr() = 0;
};/* class ExprStream */

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_STREAM_H */

