/*********************                                                        */
/*! \file theory_bags_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory rewriter.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__THEORY_BAGS_REWRITER_H
#define CVC4__THEORY__BAGS__THEORY_BAGS_REWRITER_H

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace bags {

class TheoryBagsRewriter : public TheoryRewriter
{
 public:
  RewriteResponse postRewrite(TNode node) override;

  RewriteResponse preRewrite(TNode node) override;
}; /* class TheoryBagsRewriter */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__THEORY_BAGS_REWRITER_H */
