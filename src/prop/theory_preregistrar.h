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

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class TheoryEngine;

namespace prop {

class CDCLTSatSolverInterface;
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
                     CDCLTSatSolverInterface* ss,
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
   * Notify that n is asserted from SAT solver.
   */
  void notifyAsserted(TNode n);

 private:
  /** pre-register to theory */
  void preRegisterToTheory(const std::vector<TNode>& toPreregister);
  /** Theory engine */
  TheoryEngine* d_theoryEngine;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__PREREGISTER_RLV_H */
