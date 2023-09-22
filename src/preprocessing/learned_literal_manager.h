/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Learned literal manager
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__LEARNED_LITERAL_MANAGER_H
#define CVC5__PREPROCESSING__LEARNED_LITERAL_MANAGER_H

#include "context/cdhashset.h"
#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace preprocessing {

/**
 * This class maintains the list of learned literals that have been inferred
 * during preprocessing but we have not fully processed e.g. via substitutions.
 *
 * In particular, notice that if an equality (= x t) is learned at top level,
 * we may add x -> t to top level substitutions if t does not contain x; we can
 * henceforth forget that (= x t) is a learned literal. On the other hand, if
 * a literal like (> x t) is learned at top-level, it may be useful to remember
 * this information. This class is concerned with the latter kind of literals.
 */
class LearnedLiteralManager : protected EnvObj
{
 public:
  LearnedLiteralManager(Env& env);
  /**
   * Notify learned literal. This method is called when a literal is
   * entailed by the current set of assertions.
   *
   * It should be rewritten, and such that top level substitutions have
   * been applied to it.
   */
  void notifyLearnedLiteral(TNode lit);
  /**
   * Get learned literals, which returns the current set of learned literals
   * provided to this class. These literals are refreshed so that the current
   * top-level substitutions are applied to them, and then are rewritten.
   */
  std::vector<Node> getLearnedLiterals() const;

 private:
  /** Learned literal map */
  using NodeSet = context::CDHashSet<Node>;
  /** Learned literals */
  NodeSet d_learnedLits;
};

}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__LEARNED_LITERAL_MANAGER_H */
