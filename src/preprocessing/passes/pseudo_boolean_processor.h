/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__PSEUDO_BOOLEAN_PROCESSOR_H
#define CVC5__PREPROCESSING__PASSES__PSEUDO_BOOLEAN_PROCESSOR_H

#include <optional>
#include <unordered_set>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "theory/substitutions.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class PseudoBooleanProcessor : public PreprocessingPass
{
 public:
  PseudoBooleanProcessor(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /** Assumes that the assertions have been rewritten. */
  void learn(const std::vector<Node>& assertions);

  /** Assumes that the assertions have been rewritten. */
  void applyReplacements(AssertionPipeline* assertionsToPreprocess);

  bool likelyToHelp() const;

  bool isPseudoBoolean(Node v) const;

  // Adds the fact the that integert typed variable v
  //   must be >= 0 to the context.
  // This is explained by the explanation exp.
  // exp cannot be null.
  void addGeqZero(Node v, Node exp);

  // Adds the fact the that integert typed variable v
  //   must be <= 1 to the context.
  // This is explained by the explanation exp.
  // exp cannot be null.
  void addLeqOne(Node v, Node exp);

  static inline bool isIntVar(Node v)
  {
    return v.isVar() && v.getType().isInteger();
  }

  void clear();

  /** Assumes that the assertion has been rewritten. */
  void learn(Node assertion);

  /** Rewrites a node  */
  Node applyReplacements(Node pre);

  void learnInternal(Node assertion, bool negated, Node orig);
  void learnRewrittenGeq(Node assertion, bool negated, Node orig);

  void addSub(Node from, Node to);
  void learnGeqSub(Node geq);

  static Node mkGeqOne(Node v);

  // x ->  <geqZero, leqOne>
  typedef context::CDHashMap<Node, std::pair<Node, Node>> CDNode2PairMap;
  CDNode2PairMap d_pbBounds;
  theory::SubstitutionMap d_subCache;

  typedef std::unordered_set<Node> NodeSet;
  NodeSet d_learningCache;

  context::CDO<unsigned> d_pbs;

  // decompose into \sum pos >= neg + off
  std::optional<Rational> d_off;
  std::vector<Node> d_pos;
  std::vector<Node> d_neg;

  /** Returns true if successful. */
  bool decomposeAssertion(Node assertion, bool negated);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif  // CVC5__PREPROCESSING__PASSES__PSEUDO_BOOLEAN_PROCESSOR_H
