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
 * Inst evaluator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__IEVAL__INST_EVALUATOR_H
#define CVC5__THEORY__QUANTIFIERS__IEVAL__INST_EVALUATOR_H

#include <vector>

#include "context/context.h"
#include "expr/node.h"
#include "theory/quantifiers/ieval/state.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermRegistry;

/**
 * Inst evaluator
 *
 * Incrementally maintains the state of the rewritten form of the quantified
 * formula.
 */
class InstEvaluator : protected EnvObj
{
 public:
  InstEvaluator(Env& env, QuantifiersState& qs, TermRegistry& tr, bool doCanonize = true);
  /**
   * Set that we are watching quantified formula q.
   */
  void watch(Node q);
  /** Same as above, with possibly preprocessed body. */
  void watch(Node q, Node body);
  /**
   * Set that we are considering instantiations v -> s.
   *
   * Return false if all quantified formulas watched by this class are
   * infeasible.
   *
   * If this returns true, this adds quantified formulas that are fully
   * instantiated.
   */
  void push();
  bool push(TNode v, TNode s, std::vector<Node>& assignedQuants);
  /** pop the last (successful) push */
  void pop();
  /**
   * Get instantiation for quantified formula q.
   */
  std::vector<Node> getInstantiationFor(Node q);

 private:
  /** A context object */
  context::Context d_context;
  /** The quantifiers state object */
  QuantifiersState& d_qstate;
  /** Reference to term registry */
  TermRegistry& d_treg;
  /** do canonize */
  bool d_doCanonize;
  /** The state object */
  State d_state;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__IEVAL__INST_EVALUATOR_H */
