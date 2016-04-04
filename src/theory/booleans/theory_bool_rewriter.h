/*********************                                                        */
/*! \file theory_bool_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H
#define __CVC4__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace booleans {

class TheoryBoolRewriter {

public:

  static RewriteResponse preRewrite(TNode node);
  static RewriteResponse postRewrite(TNode node);

  static void init() {}
  static void shutdown() {}

};/* class TheoryBoolRewriter */

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H */
