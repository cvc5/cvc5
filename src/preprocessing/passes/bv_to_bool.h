/*********************                                                        */
/*! \file bv_to_bool.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Yoni Zohar, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass that lifts bit-vectors of size 1 to booleans.
 **
 ** Preprocessing pass that lifts bit-vectors of size 1 to booleans.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__BV_TO_BOOL_H
#define CVC4__PREPROCESSING__PASSES__BV_TO_BOOL_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

typedef std::unordered_map<Node, Node, NodeHashFunction> NodeNodeMap;

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
    Statistics();
    ~Statistics();
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
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__BV_TO_BOOL_H */
