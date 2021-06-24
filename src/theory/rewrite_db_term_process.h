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

#ifndef CVC4__THEORY__REWRITE_DB_TERM_PROCESS__H
#define CVC4__THEORY__REWRITE_DB_TERM_PROCESS__H

#include <map>
#include <unordered_map>
#include "expr/node.h"

namespace cvc5 {
namespace theory {

/**
 * The AST structure of terms in the proof checker and in CVC4 is different.
 * This class converts between the two expected AST structures. These
 * differences include:
 * (1) CVC4 has n-ary associative operators; the proof checker assumes binary
 * applications only,
 * (2) CVC4 has (word) string literals; the proof checker assumes these are
 * concatenations of constants, e.g. "ABC" is (str.++ "A" (str.++ "B" "C")).
 *
 */
class RewriteDbTermProcess
{
 public:
  /** convert to internal
   *
   * This converts the node n to the internal shape that it would be in
   * the proof checker. This means that n-ary applications are converted
   * to (left-associative) chains.
   */
  static Node toInternal(Node n);

 private:
  /** convert to internal */
  static Node computeInternal(Node n);
};

}  // namespace theory
}  // namespace cvc5

#endif /* CVC4__THEORY__REWRITE_DB_TERM_PROCESS__H */
