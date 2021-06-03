/******************************************************************************
 * Top contributors (to current version):
 *   Makai Mann, Yoni Zohar, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The BoolToBV preprocessing pass.
 *
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__BOOL_TO_BV_H
#define CVC5__PREPROCESSING__PASSES__BOOL_TO_BV_H

#include "expr/node.h"
#include "options/bv_options.h"
#include "preprocessing/preprocessing_pass.h"
#include "util/statistics_stats.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

class BoolToBV : public PreprocessingPass
{
 public:
  BoolToBV(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  struct Statistics
  {
    IntStat d_numIteToBvite;
    IntStat d_numTermsLowered;
    IntStat d_numIntroducedItes;
    Statistics();
  };

  /** Takes an assertion and attempts to create more bit-vector structure
      by replacing boolean operators with bit-vector operators.

      It passes the allowIteIntroduction argument down to lowerNode, however it
      never allows ite introduction in the top-level assertion. There's no point
      forcing the assertion to be a bit-vector when it will just be converted
      back into a boolean.
  */
  Node lowerAssertion(const TNode& node, bool allowIteIntroduction = false);

  /** Traverses subterms to turn booleans into bit-vectors using visit
   *  Passes the allowIteIntroduction argument to visit
   *  Returns the lowered node
   */
  Node lowerNode(const TNode& node, bool allowIteIntroduction = false);

  /** Tries to lower one node to a width-one bit-vector
   *  Caches the result if successful
   *
   *  allowIteIntroduction = true causes booleans to be converted to bit-vectors
   *     using an ITE this is only used by mode ALL currently, but could
   *     conceivably be used in new modes.
   */
  void visit(const TNode& n, bool allowIteIntroduction = false);

  /* Traverses formula looking for ITEs to lower to BITVECTOR_ITE using
   * lowerNode*/
  Node lowerIte(const TNode& node);

  /** Rebuilds node using the provided kind
   *  Note: The provided kind is not necessarily different from the
   *        existing one, but still might need to be rebuilt because
   *        of subterms
   */
  void rebuildNode(const TNode& n, Kind new_kind);

  /** Updates the cache, the cache is actually supported by two maps
      one for ITEs and one for everything else

      This is necessary so that when in ITE mode, the regular cache
      can be cleared to prevent lowering boolean operators that are
      not in an ITE
   */
  void updateCache(TNode n, TNode rebuilt);

  /* Returns cached node if it exists, otherwise returns the node */
  Node fromCache(TNode n) const;

  /* Checks both caches for membership */
  bool inCache(const Node& n) const;

  /** Checks if any of the node's children were rebuilt,
   *  in which case n needs to be rebuilt as well
   */
  bool needToRebuild(TNode n) const;

  Statistics d_statistics;

  /** Keeps track of lowered ITEs
      Note: it only keeps mappings for ITEs of type bit-vector.
      Other ITEs will be in the d_lowerCache
   */
  std::unordered_map<Node, Node> d_iteBVLowerCache;

  /** Keeps track of other lowered nodes
      -- will be cleared periodically in ITE mode
  */
  std::unordered_map<Node, Node> d_lowerCache;

  /** Stores the bool-to-bv mode option */
  options::BoolToBVMode d_boolToBVMode;
};  // class BoolToBV

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5

#endif /* CVC5__PREPROCESSING__PASSES__BOOL_TO_BV_H */
