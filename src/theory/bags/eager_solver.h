/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The eager solver for bags.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__EAGER_SOLVER_H
#define CVC5__THEORY__BAGS__EAGER_SOLVER_H

#include <map>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/bags/eqc_info.h"
#include "theory/bags/solver_state.h"
#include "theory/bags/term_registry.h"
#include "theory/strings/arith_entail.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

/**
 * Eager solver, which is responsible for tracking of eager information and
 * reporting conflicts to the solver state.
 */
class EagerSolver : protected EnvObj
{
 public:
  EagerSolver(Env& env, SolverState& state, TermRegistry& treg);
  ~EagerSolver();
  /** called when a new equivalence class is created */
  void eqNotifyNewClass(TNode t);
  /** called when two equivalence classes merge */
  void eqNotifyMerge(EqcInfo* e1, TNode t1, EqcInfo* e2, TNode t2);
  /** notify fact, called when a fact is asserted to theory of bags */
  void notifyFact(TNode atom, bool polarity, TNode fact, bool isInternal);

 private:
  /**
   * Check for conflict when merging equivalence classes with the given info,
   * return true if we are in conflict.
   */
  bool checkForMergeConflict(Node a, Node b, EqcInfo* ea, EqcInfo* eb);
  /** add arithmetic bound, return true if in conflict */
  bool addArithmeticBound(EqcInfo* e, Node t, bool isLower);
  void propagateBounds(Node n);
  /** get bound for length term or regular expression membership */
  Node getBoundForLength(Node t, bool isLower) const;
  /** Reference to the solver state */
  SolverState& d_state;
  /** Reference to the term registry */
  TermRegistry& d_treg;
  /** Arithmetic entailment */
  strings::ArithEntail d_aent;
};

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__EAGER_SOLVER_H */
