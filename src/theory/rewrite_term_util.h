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
 * Rewrite term utilities
 */

#include "cvc5_private.h"

#ifndef CVC4__THEORY__REWRITE_TERM_UTIL__H
#define CVC4__THEORY__REWRITE_TERM_UTIL__H

#include <map>
#include <vector>

#include "expr/node.h"

namespace cvc5 {
namespace theory {

/** Mark variable as list */
static void markRewriteListVar(TNode fv);
/** Is list variable */
static bool isRewriteListVar(TNode fv);

}  // namespace theory
}  // namespace cvc5

#endif /* CVC4__REWRITER__TERM_UTIL__H */
