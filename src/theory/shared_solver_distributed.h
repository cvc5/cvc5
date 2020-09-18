/*********************                                                        */
/*! \file shared_solver_distributed.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Shared solver in the distributed architecture.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SHARED_SOLVER_DISTRIBUTED__H
#define CVC4__THEORY__SHARED_SOLVER_DISTRIBUTED__H

#include "expr/node.h"
#include "theory/shared_solver.h"

namespace CVC4 {
namespace theory {

/**
 * The shared solver in the distributed architecture. This class uses the
 * SharedTermsDatabase for implementing the core methods of a shared solver.
 */
class SharedSolverDistributed : public SharedSolver
{
 public:
  SharedSolverDistributed(TheoryEngine& te);
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
  /** Assert equality to the shared terms database. */
  void assertSharedEquality(TNode equality,
                            bool polarity,
                            TNode reason) override;
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
}  // namespace CVC4

#endif /* CVC4__THEORY__SHARED_SOLVER_DISTRIBUTED__H */
