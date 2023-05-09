/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Methods for counterexample-guided quantifier instantiation
 * based on nested quantifier elimination.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CEQGI__NESTED_QE_H
#define CVC5__THEORY__QUANTIFIERS__CEQGI__NESTED_QE_H

#include <unordered_set>

#include "context/cdhashmap.h"
#include "expr/node.h"

namespace cvc5::internal {

class Env;

namespace theory {
namespace quantifiers {

class NestedQe
{
  using NodeNodeMap = context::CDHashMap<Node, Node>;

 public:
  NestedQe(Env& env);
  ~NestedQe() {}
  /**
   * Process quantified formula. If this returns true, then q was processed
   * via nested quantifier elimination (either during this call or previously
   * in this user context). If q was processed in this call, the lemma:
   *   (= q qqe)
   * is added to lem, where qqe is the result of nested quantifier elimination
   * on q.
   */
  bool process(Node q, std::vector<Node>& lems);
  /**
   * Have we processed q using the above method?
   */
  bool hasProcessed(Node q) const;

  /**
   * Get nested quantification. Returns true if q has nested quantifiers.
   * Adds each nested quantifier in the body of q to nqs.
   */
  static bool getNestedQuantification(Node q, std::unordered_set<Node>& nqs);
  /**
   * Does quantified formula q have nested quantification?
   */
  static bool hasNestedQuantification(Node q);
  /**
   * Do nested quantifier elimination. Returns a formula that is equivalent to
   * q and has no nested quantification. If keepTopLevel is false, then the
   * returned formula is quantifier-free. Otherwise, it is a quantified formula
   * with no nested quantification.
   */
  static Node doNestedQe(Env& env, Node q, bool keepTopLevel = false);
  /**
   * Run quantifier elimination on quantified formula q, where q has no nested
   * quantification. This method invokes a subsolver for performing quantifier
   * elimination.
   */
  static Node doQe(Env& env, Node q);

 private:
  /** Reference to the env */
  Env& d_env;
  /**
   * Mapping from quantified formulas q to the result of doNestedQe(q, true).
   */
  NodeNodeMap d_qnqe;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
