/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewriting based on learned literals
 */
#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__LEARNED_REWRITE_H
#define CVC5__PREPROCESSING__PASSES__LEARNED_REWRITE_H

#include <iosfwd>
#include <memory>

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/arith/bound_inference.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace bags {
class BagsRewriter;
struct TableFacts;
}  // namespace bags
}  // namespace theory
namespace preprocessing {
namespace passes {

/**
 * Learned rewrites in the pass below.
 */
enum class LearnedRewriteId
{
  // Elimination of division, int division, int modulus due to non-zero
  // denominator. e.g. (not (= y 0)) => (div x y) ---> (div_total x y)
  NON_ZERO_DEN,
  // Elimination of int modulus due to range.
  // e.g. (and (<= 0 x) (< x n)) => (mod x n) ---> x
  INT_MOD_RANGE,
  // e.g. (>= c 0) => (>= p 0) ---> true where c is inferred const lower bound
  PRED_POS_LB,
  // e.g. (= c 0) => (>= p 0) ---> true where c is inferred const lower bound
  PRED_ZERO_LB,
  // e.g. (> c 0) => (>= p 0) ---> false where c is inferred const upper bound
  PRED_NEG_UB,
  // A rule of the bags rewriter that reads a key or a NOT NULL column of a
  // table constant, which learned literals state (see
  // theory::bags::TableFacts), e.g. for column 0 a key of X, i.e.
  // (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X)) =>
  // (bag.setof ((_ table.project 0 1) X)) ---> ((_ table.project 0 1) X)
  BAGS_TABLE_FACTS,

  //-------------------------------------- NONE
  NONE
};

/**
 * Converts an learned rewrite id to a string.
 *
 * @param i The learned rewrite identifier
 * @return The name of the learned rewrite identifier
 */
const char* toString(LearnedRewriteId i);

/**
 * Writes an learned rewrite identifier to a stream.
 *
 * @param out The stream to write to
 * @param i The learned rewrite identifier to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, LearnedRewriteId i);

/**
 * Applies learned rewriting. This rewrites the input based on learned literals.
 * This in particular does rewriting that goes beyond what is done in
 * non-clausal simplification, where equality substitutions + constant
 * propagations are performed. In particular, this pass applies rewriting
 * based on e.g. bound inference for arithmetic, and on the keys and NOT NULL
 * columns of tables (theory::bags::TableFacts), which the rewriter of the
 * bags theory does not know.
 */
class LearnedRewrite : public PreprocessingPass
{
 public:
  LearnedRewrite(PreprocessingPassContext* preprocContext);
  ~LearnedRewrite();

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /**
   * Apply rewrite with learned literals, traverses n.
   */
  Node rewriteLearnedRec(Node n,
                         theory::arith::BoundInference& binfer,
                         const std::vector<Node>& learnedLits,
                         std::unordered_set<Node>& lems,
                         std::unordered_map<TNode, Node>& visited);
  /**
   * Learned rewrite to n, single step.
   */
  Node rewriteLearned(Node n,
                      theory::arith::BoundInference& binfer,
                      const std::vector<Node>& learnedLits);
  /**
   * Learned rewrite of a term of the bags theory by the keys and NOT NULL
   * columns of tables (d_tableFacts). For column 0 a key of X,
   *   (bag.setof ((_ table.project 0 1) X)) ---> ((_ table.project 0 1) X)
   * The result is rewritten again, by rewriteLearnedRec, since the rules
   * build terms that the facts or the rewriter may rewrite further.
   */
  Node rewriteLearnedBags(Node n,
                          theory::arith::BoundInference& binfer,
                          const std::vector<Node>& learnedLits,
                          std::unordered_set<Node>& lems);
  /** Return learned rewrite */
  Node returnRewriteLearned(Node n, Node nr, LearnedRewriteId id);
  /**
   * The keys and NOT NULL columns of tables that the learned literals state,
   * and a bags rewriter that reads them. Both are null unless the bags
   * theory is enabled and some learned literal states one.
   */
  std::unique_ptr<theory::bags::TableFacts> d_tableFacts;
  std::unique_ptr<theory::bags::BagsRewriter> d_bagsRewriter;
  /** the nesting of rewriteLearnedBags */
  size_t d_bagsDepth = 0;
  /** Counts number of applications of learned rewrites */
  HistogramStat<LearnedRewriteId> d_lrewCount;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__LEARNED_REWRITE_H */
