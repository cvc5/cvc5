/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * FiniteFields theory rewriter.
 */

#include "theory/ff/theory_ff_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

RewriteResponse TheoryFiniteFieldsRewriter::postRewrite(TNode t)
{
  Trace("ff::rw::post") << "ff::postRewrite: " << t << std::endl;
  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse TheoryFiniteFieldsRewriter::preRewrite(TNode t)
{
  Trace("ff::rw::pre") << "ff::preRewrite: " << t << std::endl;
  return RewriteResponse(REWRITE_DONE, t);
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
