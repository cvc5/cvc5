/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A rewriter that does nothing
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__IDL__NOOP_REWRITER_H
#define CVC5__THEORY__ARITH__IDL__NOOP_REWRITER_H

#include "theory/theory_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace idl {

class NoopRewriter : public TheoryRewriter
{
 public:
  RewriteResponse preRewrite(TNode n) override
  {
    return RewriteResponse(REWRITE_DONE, n);
  }

  RewriteResponse postRewrite(TNode n) override
  {
    NodeManager* nm = NodeManager::currentNM();
    if (n.getKind() == Kind::NEG)
    {
      Node x = n[0];
      if (x.getKind() == Kind::CONST_RATIONAL)
      {
        return RewriteResponse(REWRITE_DONE,
                               nm->mkConstInt(-x.getConst<Rational>()));
      }
    }
    return RewriteResponse(REWRITE_DONE, n);
  }
}; /* class NoopRewriter */

}  // namespace idl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ARITH__IDL__NOOP_REWRITER_H */
