/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Techniques for evaluating terms with recursively defined functions.
 */

#include "cvc5_private.h"

#ifndef CVC5__QUANTIFIERS_FUN_DEF_EVALUATOR_H
#define CVC5__QUANTIFIERS_FUN_DEF_EVALUATOR_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Techniques for evaluating recursively defined functions.
 */
class FunDefEvaluator : protected EnvObj
{
 public:
  FunDefEvaluator(Env& env);
  ~FunDefEvaluator() {}
  /**
   * Assert definition of a (recursive) function definition given by quantified
   * formula q.
   */
  void assertDefinition(Node q);
  /**
   * Simplify node based on the (recursive) function definitions known by this
   * class. If n cannot be simplified to a constant, then this method returns
   * null.
   */
  Node evaluateDefinitions(Node n) const;
  /**
   * Has a call to assertDefinition been made? If this returns false, then
   * the evaluate method is the same as calling the rewriter, and returning
   * false if the result is non-constant.
   */
  bool hasDefinitions() const;

  /** Get definitions */
  const std::vector<Node>& getDefinitions() const;
  /** Get definition for function symbol f, if it is cached by this class */
  Node getDefinitionFor(Node f) const;

 private:
  /** information cached per function definition */
  class FunDefInfo
  {
   public:
    /** the quantified formula */
    Node d_quant;
    /** the body */
    Node d_body;
    /** the formal argument list */
    std::vector<Node> d_args;
  };
  /** maps functions to the above information */
  std::map<Node, FunDefInfo> d_funDefMap;
  /** list of all definitions */
  std::vector<Node> d_funDefs;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
