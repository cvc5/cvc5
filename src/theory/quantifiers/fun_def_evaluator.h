/*********************                                                        */
/*! \file fun_def_evaluator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Techniques for evaluating terms with recursively defined functions.
 **/

#include "cvc4_private.h"

#ifndef CVC4__QUANTIFIERS_FUN_DEF_EVALUATOR_H
#define CVC4__QUANTIFIERS_FUN_DEF_EVALUATOR_H

#include <map>
#include <vector>
#include "expr/node.h"
#include "theory/evaluator.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * Techniques for evaluating recursively defined functions.
 */
class FunDefEvaluator
{
 public:
  FunDefEvaluator();
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
  Node evaluate(Node n) const;
  /**
   * Has a call to assertDefinition been made? If this returns false, then
   * the evaluate method is the same as calling the rewriter, and returning
   * false if the result is non-constant.
   */
  bool hasDefinitions() const;

 private:
  /** information cached per function definition */
  class FunDefInfo
  {
   public:
    /** the body */
    Node d_body;
    /** the formal argument list */
    std::vector<Node> d_args;
  };
  /** maps functions to the above information */
  std::map<Node, FunDefInfo> d_funDefMap;
  /** evaluator utility */
  Evaluator d_eval;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
