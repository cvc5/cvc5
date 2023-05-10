/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewrite database term processor
 */

#include "cvc5_private.h"

#ifndef CVC4__REWRITER__REWRITE_DB_TERM_PROCESS__H
#define CVC4__REWRITER__REWRITE_DB_TERM_PROCESS__H

#include <map>
#include <unordered_map>

#include "expr/node.h"
#include "expr/node_converter.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * The desired AST of terms in our DSL rewrite rule proof reconstruction can be
 * different than the default representation of terms in cvc5. These
 * differences include:
 * (1) cvc5 has (word) string literals; the DSL assumes these are
 * concatenations of constants, e.g. "ABC" is the term (str.++ "A" "B" "C").
 *
 * This node converter converts from the default representation of cvc5 terms
 * to the representation of terms required by the DSL proof reconstruction
 * algorithm.
 *
 * Notice that this converter is independent of the end target proof checker,
 * and thus we do not do any target-specific processing (e.g. converting to
 * curried form).
 */
class RewriteDbNodeConverter : public NodeConverter
{
 public:
  /**
   * This converts the node n to the internal shape that it should be in
   * for the DSL proof reconstruction algorithm.
   */
  Node postConvert(Node n) override;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC4__THEORY__REWRITE_DB_TERM_PROCESS__H */
