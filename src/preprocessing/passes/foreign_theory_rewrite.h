/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The foreign_theory_rewrite preprocessing pass.
 *
 * Simplifies nodes of one theory using rewrites from another.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__FOREIGN_THEORY_REWRITE_H
#define CVC5__PREPROCESSING__PASSES__FOREIGN_THEORY_REWRITE_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using CDNodeMap = context::CDHashMap<Node, Node>;

class ForeignTheoryRewriter : protected EnvObj
{
 public:
  ForeignTheoryRewriter(Env& env);
  /** the main function that simplifies n.
   * does a traversal on n and call rewriting fucntions.
   */
  Node simplify(Node n);
  /** A specific simplification function specific for GEQ
   * constraints in strings.
   */
  Node rewriteStringsGeq(Node n);
  /** invoke rewrite functions for n.
   * based on the structure of n (typically its kind)
   * we invoke rewrites from other theories.
   * For example: when encountering a `>=` node,
   * we invoke rewrites from the theory of strings.
   */
  Node foreignRewrite(Node n);
  /** construct a node with the same operator as originalNode whose children are
   * processedChildren
   */
  static Node reconstructNode(Node originalNode, std::vector<Node> newChildren);
  /** A cache to store the simplified nodes */
  CDNodeMap d_cache;
};

class ForeignTheoryRewrite : public PreprocessingPass
{
 public:
  ForeignTheoryRewrite(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /** Foreign theory rewriter */
  ForeignTheoryRewriter d_ftr;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__FOREIGN_THEORY_REWRITE_H */
