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
 * Preregister policy
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__THEORY_PREREGISTRAR_H
#define CVC5__PROP__THEORY_PREREGISTRAR_H

#include <vector>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class TheoryEngine;

namespace prop {

class CDCLTSatSolver;
class CnfStream;

/**
 * Implements the policy for preregistration to TheoryEngine based on
 * notifications from the SAT solver.
 */
class TheoryPreregistrar : protected EnvObj
{
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
   */
  void notifySatLiteral(TNode n);
  /**
   * Notify that n is asserted from SAT solver, return true if we should
   * assert n to the theory engine.
   *
   * An example of when this method returns false is when n is a Boolean
   * variable that does not have kind BOOLEAN_TERM_VARIABLE. Note we only
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
   * Keep track of sat literals that were registered at a SAT context level > 0
   * and need reregistration when we backtrack to a lower level than the level
   * they were registered at. SAT variables stay in the SAT solver (until they
   * are popped via a user-context-level pop), and we have to ensure that they
   * are registered at all times on the theory level.
   *
   * This is dependent on the user context.
   */
  context::CDHashMap<Node, uint32_t> d_sat_literals;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__PREREGISTER_RLV_H */
