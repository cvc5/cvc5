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
 * Preregister policy
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__THEORY_PREREGISTRAR_H
#define CVC5__PROP__THEORY_PREREGISTRAR_H

#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class TheoryEngine;

namespace prop {

class CDCLTSatSolver;
class CnfStream;
class TheoryPreregistrarNotify;

/**
 * Implements the policy for preregistration to TheoryEngine based on
 * notifications from the SAT solver.
 */
class TheoryPreregistrar : protected EnvObj
{
  friend TheoryPreregistrarNotify;

 public:
  TheoryPreregistrar(Env& env,
                     TheoryEngine* te,
                     CDCLTSatSolver* ss,
                     CnfStream* cs);
  ~TheoryPreregistrar();
  /** Do we need to be informed of activated skolem definitions? */
  bool needsActiveSkolemDefs() const;
  /** theory check */
  void check();
  /** Notify assertion */
  void addAssertion(TNode n, TNode skolem, bool isLemma);
  /** Notify that skolem definitions have become active */
  void notifyActiveSkolemDefs(std::vector<TNode>& defs);
  /**
   * Notify that a SAT literal for atom n has been allocated in the SAT solver.
   * @param n The node to preregister.
   */
  void notifySatLiteral(TNode n);
  /**
   * Callback to notify that the SAT solver backtracked by the given number
   * of levels.
   * @param nlevels The number of levels the SAT solver backtracked.
   */
  void notifyBacktrack(uint32_t nlevels);
  /**
   * Notify that n is asserted from SAT solver, return true if we should
   * assert n to the theory engine.
   *
   * An example of when this method returns false is when n is a Boolean
   * variable that does not have skolem function id PURIFY (which marks that
   * it requires sending to the theory). Note we only
   * call this method for such terms when the TRACK_AND_NOTIFY(_VAR) policy
   * is used in the CNF stream.
   */
  bool notifyAsserted(TNode n);

 private:
  /** pre-register to theory */
  void preRegisterToTheory(const std::vector<TNode>& toPreregister);
  /** Theory engine */
  TheoryEngine* d_theoryEngine;
  /**
   * Cache preregistered SAT literals, mapped to the SAT context level they
   * were registered at. On backtrack, all literals that were registered at
   * a level higher than the current (backtracked) level need registration.
   * This is due to the fact that they get popped from the SAT context on
   * backtrack but remain in the SAT solver.
   * This cache is cleared on user context pop.
   */
  std::vector<std::pair<Node, uint32_t>> d_sat_literals;
  /* Notifies on SAT context pop. */
  std::unique_ptr<TheoryPreregistrarNotify> d_notify;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__PREREGISTER_RLV_H */
