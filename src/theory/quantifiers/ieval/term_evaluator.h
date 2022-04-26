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

class QuantifiersState;
class TermDb;

namespace ieval {

/** The evaluator to use */
enum class TermEvaluatorMode : uint32_t
{
  // do not use an evaluator
  NONE,
  // we are looking for conflicts
  CONFLICT,
  // we are looking for propagating instances
  PROP,
  // we are looking for instances that are not entailed
  NO_ENTAIL,
  // model evaluator
  MODEL,
};

class State;

class TermEvaluator : protected EnvObj
{
 public:
  TermEvaluator(Env& env, TermEvaluatorMode tev);
  /**
   * Evaluate base child
   * Called on nodes n with no children, or for terms that we treat as
   * black boxes, e.g. closures.
   */
  virtual TNode evaluateBase(const State& s, TNode n) = 0;
  /**
   * Partial evaluate child.
   * Called when a given child of n has been assigned val.
   */
  virtual TNode partialEvaluateChild(const State& s,
                                     TNode n,
                                     TNode child,
                                     TNode val) = 0;
  /**
   * Evaluate term
   * Called when all children of n have been assigned values childValues.
   */
  virtual TNode evaluate(const State& s,
                         TNode n,
                         const std::vector<TNode>& childValues) = 0;
protected:
  /** The mode */
  TermEvaluatorMode d_tevMode;
};

class TermEvaluatorEntailed : public TermEvaluator
{
 public:
  TermEvaluatorEntailed(Env& env, TermEvaluatorMode tev, QuantifiersState& qs, TermDb& tdb);
  /** Evaluate base */
  TNode evaluateBase(const State& s, TNode n) override;
  /** Partial evaluate child */
  TNode partialEvaluateChild(const State& s,
                             TNode n,
                             TNode child,
                             TNode val) override;
  /** Evaluate term */
  TNode evaluate(const State& s,
                 TNode n,
                 const std::vector<TNode>& childValues) override;

 private:
  /** Quantifiers state */
  QuantifiersState& d_qs;
  /** Pointer to the term database */
  TermDb& d_tdb;
  /** Whether we are using an optimization for checking the relevant domain */
  bool d_checkRelDom;
};

#if 0
class TermEvaluatorModel : public TermEvaluator
{
public:
  TermEvaluatorModel(Env& env, TermDb* tdb);
  /** Evaluate base */
  Node evaluateBase(const State& s, Node n) override;
  /** Partial evaluate child */
  Node partialEvaluateChild(const State& s, Node n, TNode child, TNode val) override;
  /** Evaluate term */
  Node evaluate(const State& s, Node n, const std::vector<TNode>& childValues) override;
private:
  TermDb* d_tdb;
};
#endif

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__IEVAL__TERM_EVALUATOR_CALLBACK_H */
