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
 * Shared solver in the distributed architecture.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SHARED_SOLVER_DISTRIBUTED__H
#define CVC5__THEORY__SHARED_SOLVER_DISTRIBUTED__H

#include "expr/node.h"
#include "theory/shared_solver.h"

namespace cvc5::internal {
namespace theory {

/**
 * The shared solver in the distributed architecture. This class uses the
 * SharedTermsDatabase for implementing the core methods of a shared solver.
 */
class SharedSolverDistributed : public SharedSolver
{
 public:
  SharedSolverDistributed(Env& env, TheoryEngine& te);
  virtual ~SharedSolverDistributed() {}
  //------------------------------------- initialization
  /**
   * Returns true if we need an equality engine, this has the same contract
   * as Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(theory::EeSetupInfo& esi) override;
  /** Set equality engine in the shared terms database */
  void setEqualityEngine(eq::EqualityEngine* ee) override;
  //------------------------------------- end initialization
  /** Assert n to the shared terms database. */
  void assertShared(TNode n, bool polarity, TNode reason) override;
  /**
   * Get equality status based on the equality engine of shared terms database
   */
  EqualityStatus getEqualityStatus(TNode a, TNode b) override;
  /** Explain literal that was propagated by a theory or using shared terms
   * database */
  TrustNode explain(TNode literal, TheoryId id) override;

 protected:
  /** If t is an equality, add it as one that may be propagated */
  void preRegisterSharedInternal(TNode t) override;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SHARED_SOLVER_DISTRIBUTED__H */
