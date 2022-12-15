/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model normal form finder for strings
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__MODEL_CONS_H
#define CVC5__THEORY__STRINGS__MODEL_CONS_H

#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/**
 */
class ModelCons : protected EnvObj
{
 public:
  ModelCons(Env& env) : EnvObj(env) {}
  virtual ~ModelCons() {}
  /**
   * Has candidate model? Returns true if we can definitely construct a model
   * that is ready to check at LAST_CALL effort. In other words, if this is
   * true, then we can abort a FULL effort check.
   */
  virtual bool hasCandidateModel() = 0;

  /** Get string representatives from */
  virtual void getStringRepresentativesFrom(
      const std::set<Node>& termSet,
      std::unordered_set<TypeNode>& repTypes,
      std::map<TypeNode, std::unordered_set<Node>>& repSet,
      std::vector<Node>& auxEq) = 0;
  /** Separate by length
   *
   * Separate the string representatives in argument n into a partition cols
   * whose collections have equal length. The i^th vector in cols has length
   * lts[i] for all elements in col. These vectors are furthmore separated
   * by string-like type.
   *
   * Must assign lts to *concrete* lengths.
   */
  virtual void separateByLength(const std::vector<Node>& n,
                                std::vector<std::vector<Node>>& cols,
                                std::vector<Node>& lts) = 0;
  /**
   * Get the normal form
   */
  virtual std::vector<Node> getNormalForm(Node n) = 0;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__MODEL_CONS_H */
