/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for verifying models.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__MODEL_VERIFIER_H
#define CVC5__SMT__MODEL_VERIFIER_H

#include <unordered_set>

#include "context/cdlist.h"
#include "expr/node.h"
#include "expr/subs.h"
#include "smt/env_obj.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

namespace theory {
class TheoryModel;
}

namespace smt {

/**
 * This utility is responsible for verifying that a candidate model satisfies
 * the input assertions.
 *
 * In contrast to CheckModels, which is a debugging utility that issues
 * warnings when a model cannot be checked, this utility is conservative: it
 * returns true only if it was able to establish that the given model is a
 * satisfying assignment for the input assertions. It is used for strengthening
 * "unknown" responses to "sat".
 *
 * The verification it performs does not rely on the internal state of the
 * theory solvers. Instead, it computes the model value of each symbol
 * occurring in the input assertions, substitutes these values into the
 * assertions and requires that the result rewrites to true. Thus, its
 * conclusions are trustworthy up to the correctness of the rewriter, and are
 * independent of e.g. how truth values were assigned to quantified formulas or
 * to applications of unevaluatable operators.
 */
class ModelVerifier : protected EnvObj
{
 public:
  ModelVerifier(Env& e);
  /**
   * Verify that model m satisfies the input assertions al.
   *
   * @param m The model to verify.
   * @param al The input assertions.
   * @return true if we successfully verified that m satisfies al. Note that
   * returning false does not imply that m is not a model of al, it only means
   * that we were not able to verify this.
   */
  bool verify(theory::TheoryModel* m, const context::CDList<Node>& al);

 private:
  /**
   * Add the model values of the symbols occurring in n to the substitution
   * mvs, if they have not been added already.
   *
   * @param m The model.
   * @param n The term whose symbols we are processing.
   * @param mvs The substitution mapping symbols to their model values.
   * @param processed The symbols we have already added to mvs.
   * @return false if the model value of a symbol of n could not be determined,
   * in which case we cannot verify assertions containing n.
   */
  bool addModelValues(theory::TheoryModel* m,
                      const Node& n,
                      Subs& mvs,
                      std::unordered_set<Node>& processed);
  /** Time spent in calls to verify */
  TimerStat d_verifyTime;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
