/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The eager solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__EAGER_SOLVER_H
#define CVC5__THEORY__STRINGS__EAGER_SOLVER_H

#include <map>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/eqc_info.h"
#include "theory/strings/regexp_entail.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/term_registry.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

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
  /** notify fact, called when a fact is asserted to theory of strings */
  void notifyFact(TNode atom, bool polarity, TNode fact, bool isInternal);

 private:
  /** add endpoints to eqc info
   *
   * This method is called when term t is the explanation for why equivalence
   * class eqc may have a constant endpoint due to a concatentation term concat.
   * For example, we may call this method on:
   *   t := (str.++ x y), concat := (str.++ x y), eqc
   * for some eqc that is currently equal to t. Another example is:
   *   t := (str.in.re z (re.++ r s)), concat := (re.++ r s), eqc
   * for some eqc that is currently equal to z.
   *
   * Returns true if we are in conflict, that is, a conflict was sent via the
   * inference manager.
   */
  bool addEndpointsToEqcInfo(Node t, Node concat, Node eqc);
  /**
   * Check for conflict when merging equivalence classes with the given info,
   * return true if we are in conflict.
   */
  bool checkForMergeConflict(Node a, Node b, EqcInfo* ea, EqcInfo* eb);
  /** add endpoint constant, return true if in conflict */
  bool addEndpointConst(EqcInfo* e, Node t, Node c, bool isSuf);
  /** add arithmetic bound, return true if in conflict */
  bool addArithmeticBound(EqcInfo* e, Node t, bool isLower);
  /** get bound for length term or regular expression membership */
  Node getBoundForLength(Node t, bool isLower) const;
  /** Reference to the solver state */
  SolverState& d_state;
  /** Reference to the term registry */
  TermRegistry& d_treg;
  /** Arithmetic entailment */
  ArithEntail d_aent;
  /** Regular expression entailment */
  RegExpEntail d_rent;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__EAGER_SOLVER_H */
