/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for checking for illegal inputs
 */

#include "cvc5_private.h"

#ifndef __CVC5__THEORY__ILLEGAL_CHECKER_H
#define __CVC5__THEORY__ILLEGAL_CHECKER_H

#include <cvc5/cvc5_types.h>

#include <unordered_set>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "smt/assertions.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace smt {

/**
 * A utility for determining whether inputs to the solver engine are illegal.
 */
class IllegalChecker : protected EnvObj
{
 public:
  IllegalChecker(Env& e);
  /**
   * Check whether the given assertions are legal. We check only the new
   * assertions in the assertion list of as, in a user-context-dependent manner.
   */
  void checkAssertions(Assertions& as);

 private:
  /** The assertions we have visited (user-context dependent) */
  context::CDHashSet<Node> d_visited;
  /** The illegal kinds that cannot appear in assertions */
  std::unordered_set<Kind, kind::KindHashFunction> d_illegalKinds;
  /**
   * Illegal types. We only require adding atomic types (e.g. RoundingMode)
   * to this set, as their kind is TYPE_CONSTANT, which cannot be excluded.
   */
  std::unordered_set<TypeNode> d_illegalTypes;
  /** The index up to the index in the assertions we have checked */
  context::CDO<size_t> d_assertionIndex;
  /**
   * Check internal, which traverses the term to look for illegal
   * terms.
   */
  Kind checkInternal(TNode n);
};

}  // namespace smt
}  // namespace cvc5::internal

#endif /* __CVC5__THEORY__ILLEGAL_CHECKER_H */
