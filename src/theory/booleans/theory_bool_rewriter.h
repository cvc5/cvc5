/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H
#define CVC5__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H

#include "theory/theory_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace booleans {

class TheoryBoolRewriter : public TheoryRewriter
{
 public:
  RewriteResponse preRewrite(TNode node) override;
  RewriteResponse postRewrite(TNode node) override;

}; /* class TheoryBoolRewriter */

}  // namespace booleans
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H */
