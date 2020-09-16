/*********************                                                        */
/*! \file theory_fp_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Martin Brain, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

#ifndef CVC4__THEORY__FP__THEORY_FP_REWRITER_H
#define CVC4__THEORY__FP__THEORY_FP_REWRITER_H

#include "theory/theory_rewriter.h"

namespace CVC4 {
namespace theory {
namespace fp {

typedef RewriteResponse (*RewriteFunction) (TNode, bool);

class TheoryFpRewriter : public TheoryRewriter
{
 public:
  TheoryFpRewriter();

  RewriteResponse preRewrite(TNode node) override;
  RewriteResponse postRewrite(TNode node) override;

  /**
   * Rewrite an equality, in case special handling is required.
   */
  Node rewriteEquality(TNode equality)
  {
    // often this will suffice
    return postRewrite(equality).d_node;
  }

 protected:
  RewriteFunction d_preRewriteTable[kind::LAST_KIND];
  RewriteFunction d_postRewriteTable[kind::LAST_KIND];
  RewriteFunction d_constantFoldTable[kind::LAST_KIND];
}; /* class TheoryFpRewriter */

}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__FP__THEORY_FP_REWRITER_H */
