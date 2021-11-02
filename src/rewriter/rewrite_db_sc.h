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
 * Rewrite database side conditions
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__REWRITE_DB_SC__H
#define CVC5__REWRITER__REWRITE_DB_SC__H

#include <map>
#include <vector>

#include "expr/node.h"

namespace cvc5 {
namespace rewriter {

/**
 * Management of side conditions for rewrite rules.
 */
class RewriteDbSc
{
 public:
  RewriteDbSc();
  ~RewriteDbSc() {}
  /** is side condition */
  static bool isSideCondition(Node f);
  /** run side condition */
  static Node evaluate(Node f, const std::vector<Node>& args);
};

}  // namespace rewriter
}  // namespace cvc5

#endif /* CVC5__THEORY__REWRITE_DB_SC__H */
