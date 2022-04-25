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

#include "context/cdhashmap.h"
#include "context/context.h"
#include "expr/node.h"
#include "expr/term_canonize.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/ieval/state.h"
#include "theory/quantifiers/ieval/term_evaluator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermRegistry;

namespace ieval {

/**
 * Inst evaluator
 *
 * Incrementally maintains the state of the rewritten form of the quantified
 * formula.
 *
 * To use, you must:
 * - Construct
 * - Set a evaluator mode
 * - Watch quantified formulas
 * - push/pop variable assignments
 */
class InstEvaluator : protected EnvObj
{
  using NodeNodeMap = context::CDHashMap<Node, Node>;

 public:
  InstEvaluator(Env& env,
                QuantifiersState& qs,
                TermRegistry& tr,
                bool doCanonize = false,
                bool trackAssignedQuant = false);
  /**
   * Set that we are watching quantified formula q. This can only be done if
   * there are no variable assignments yet.
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
  bool push(TNode v, TNode s);
  bool push(TNode v, TNode s, std::vector<Node>& assignedQuants);
  /** pop the last (successful) push */
  void pop();
  /** full reset */
  void resetAll();
  /**
   * Get instantiation for quantified formula q.
   */
  std::vector<Node> getInstantiationFor(Node q) const;
  /**
   * Get failure explanation for q, return a vector of terms whose size
   * is equal to the number of variables of q. Null nodes in this vector
   * indicate that we did not depend on the value of that variable.
   */
  std::vector<Node> getFailureExp(Node q) const;
  /**
   * Is feasible, return true if any quantified formulas are feasible.
   */
  bool isFeasible() const;
  /**
   * Set evaluator mode. This can be modified if there are no variable
   * assignments.
   */
  void setEvaluatorMode(TermEvaluatorMode tev);

 private:
  /** push internal */
  bool pushInternal(TNode v, TNode s, std::vector<Node>& assignedQuants);
  /** A context object */
  context::Context d_context;
  /** do canonize */
  bool d_doCanonize;
  /** Are we tracking unassigned quantifiers? */
  bool d_trackAssignedQuant;
  /** The state object */
  State d_state;
  /** Variable mapping */
  NodeNodeMap d_varMap;
  /** Term canonizer */
  expr::TermCanonize d_tcanon;
};

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__IEVAL__INST_EVALUATOR_H */
