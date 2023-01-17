/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewrite database
 */

#include "rewriter/rewrite_db.h"

#include "expr/node_algorithm.h"
#include "rewriter/rewrites.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

RewriteDb::RewriteDb()
{
  rewriter::addRules(*this);
}

void RewriteDb::addRule(DslPfRule id,
                        const std::vector<Node> fvs,
                        Node a,
                        Node b,
                        Node cond,
                        Node context,
                        bool isFlatForm)
{
}


}  // namespace rewriter
}  // namespace cvc5::internal
