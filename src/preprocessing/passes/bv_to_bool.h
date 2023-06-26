/******************************************************************************
 * Top contributors (to current version):
 *   Liana Hadarean, Yoni Zohar, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Preprocessing pass that lifts bit-vectors of size 1 to booleans.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__BV_TO_BOOL_H
#define CVC5__PREPROCESSING__PASSES__BV_TO_BOOL_H

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

typedef std::unordered_map<Node, Node> NodeNodeMap;

class BVToBool : public PreprocessingPass
{

 public:
  BVToBool(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  struct Statistics
  {
    IntStat d_numTermsLifted;
    IntStat d_numAtomsLifted;
    IntStat d_numTermsForcedLifted;
    Statistics(StatisticsRegistry& reg);
  };
  void addToBoolCache(TNode term, Node new_term);
  Node getBoolCache(TNode term) const;
  bool hasBoolCache(TNode term) const;

  void addToLiftCache(TNode term, Node new_term);
  Node getLiftCache(TNode term) const;
  bool hasLiftCache(TNode term) const;

  bool isConvertibleBvTerm(TNode node);
  bool isConvertibleBvAtom(TNode node);
  Node convertBvAtom(TNode node);
  Node convertBvTerm(TNode node);
  Node liftNode(TNode current);
  void liftBvToBool(const std::vector<Node>& assertions,
                    std::vector<Node>& new_assertions);

  NodeNodeMap d_liftCache;
  NodeNodeMap d_boolCache;
  Node d_one;
  Node d_zero;
  Statistics d_statistics;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__BV_TO_BOOL_H */
