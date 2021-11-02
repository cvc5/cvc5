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
 * Rewrite database term processor
 */

#include "cvc5_private.h"

#ifndef CVC4__REWRITER__REWRITE_DB_TERM_PROCESS__H
#define CVC4__REWRITER__REWRITE_DB_TERM_PROCESS__H

#include <map>
#include <unordered_map>

#include "expr/node.h"
#include "expr/node_converter.h"

namespace cvc5 {
namespace rewriter {

/**
 * The AST structure of terms in the proof checker and in cvc5 is different.
 * This class converts between the two expected AST structures. These
 * differences include:
 * (1) cvc5 has (word) string literals; the proof checker assumes these are
 * concatenations of constants, e.g. "ABC" is the term (str.++ "A" "B" "C").
 * Notice that we do not convert to n-ary form (as required by e.g. LFSC)
 * here.
 */
class RewriteDbNodeConverter : public NodeConverter
{
 public:
  /** convert to internal
   *
   * This converts the node n to the internal shape that it would be in
   * the proof checker. This means that n-ary applications are converted
   * to (left-associative) chains.
   */
  Node postConvert(Node n) override;
};

}  // namespace rewriter
}  // namespace cvc5

#endif /* CVC4__THEORY__REWRITE_DB_TERM_PROCESS__H */
