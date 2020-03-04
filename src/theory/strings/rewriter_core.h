/*********************                                                        */
/*! \file rewriter_core.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Core functions for the rewriter of the theory of strings
 **
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__REWRITER_CORE_H
#define CVC4__THEORY__STRINGS__REWRITER_CORE_H

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace strings {

class RewriterCore
{
public:
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
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__REWRITER_CORE_H */
