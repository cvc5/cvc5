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
 * Term evaluator callback class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__IEVAL__TERM_EVALUATOR_CALLBACK_H
#define CVC5__THEORY__QUANTIFIERS__IEVAL__TERM_EVALUATOR_CALLBACK_H

#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
  
class TermDb;

namespace ieval {

class State;

class TermEvaluatorCallback : protected EnvObj
{
public:
  TermEvaluatorCallback(Env& env);
  /**
   * Evaluate base child
   * Called on nodes n with no children, or for terms that we treat as
   * black boxes, e.g. closures.
   */
  virtual Node evaluateBase(State& s, Node n) = 0;
  /** 
   * Partial evaluate child.
   * Called when a given child of n has been assigned val.
   */
  virtual Node partialEvaluateChild(State& s, Node n, TNode child, TNode val) = 0;
  /**
   * Evaluate term
   * Called when all children of n have been assigned values childValues.
   */
  virtual Node evaluate(State& s, Node n, const std::vector<TNode>& childValues) = 0;
};

class TermEvaluatorCallbackEntailed : public TermEvaluatorCallback
{
public:
  TermEvaluatorCallbackEntailed(Env& env, QuantifiersState& qs, TermDb* tdb);
  /** Evaluate base */
  Node evaluateBase(State& s, Node n) override;
  /** Partial evaluate child */
  Node partialEvaluateChild(State& s, Node n, TNode child, TNode val) override;
  /** Evaluate term */
  Node evaluate(State& s, Node n, const std::vector<TNode>& childValues) override;
private:
  /** Quantifiers state */
  QuantifiersState& d_qstate;
  /** Pointer to the term database */
  TermDb* d_tdb;
};

#if 0
class TermEvaluatorCallbackModel : public TermEvaluatorCallback
{
public:
  TermEvaluatorCallbackModel(Env& env, TermDb* tdb);
  /** Evaluate base */
  Node evaluateBase(State& s, Node n) override;
  /** Partial evaluate child */
  Node partialEvaluateChild(State& s, Node n, TNode child, TNode val) override;
  /** Evaluate term */
  Node evaluate(State& s, Node n, const std::vector<TNode>& childValues) override;
private:
  TermDb* d_tdb;
};
#endif

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__IEVAL__TERM_EVALUATOR_CALLBACK_H */
