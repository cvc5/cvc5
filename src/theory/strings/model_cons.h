/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
 * The base class for strings model construction. This is used by TheoryStrings
 * during collectModeValues for specifying how to construct model values
 * for string-like terms.
 */
class ModelCons : protected EnvObj
{
 public:
  ModelCons(Env& env) : EnvObj(env) {}
  virtual ~ModelCons() {}

  /**
   * Get string representatives from relevant term set.
   *
   * Based on the current set of relevant terms in termSet, this gets all
   * representatives of string-like type to be used for model construction,
   * and groups them by type.
   *
   * @param termSet The relevant term set
   * @param repTypes The set of types of terms in the domain of repSet
   * @param repSet Map from types to the representatives of that type
   * @param auxEq A list of equalities to assert directly to the model, e.g.
   * if some term was equated to another.
   */
  virtual void getStringRepresentativesFrom(
      const std::set<Node>& termSet,
      std::unordered_set<TypeNode>& repTypes,
      std::map<TypeNode, std::unordered_set<Node>>& repSet,
      std::vector<Node>& auxEq) = 0;
  /**
   * Separate by length.
   *
   * Separate the string representatives in argument n into a partition cols
   * whose collections have equal length. The i^th vector in cols has length
   * lts[i] for all elements in col.
   *
   * Must assign lts to *concrete* lengths.
   */
  virtual void separateByLength(const std::vector<Node>& n,
                                std::vector<std::vector<Node>>& cols,
                                std::vector<Node>& lts) = 0;
  /**
   * Get the normal form for n. If the returned vector has length > 1, then the
   * model value for (all variables in) the equivalence class of n will be
   * assigned to the model value based on this list. If the returned vector
   * has length 0, the equivalence class will be assigned the empty string.
   * If the returned vector has size 1 and contains a constant, the equivalence
   * class will be assigned that constant. Otherwise, the equivalence class
   * will be assigned an arbitrary value whose length was determined by
   * a call to separateByLength.
   */
  virtual std::vector<Node> getNormalForm(Node n) = 0;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__MODEL_CONS_H */
