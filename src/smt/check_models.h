/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for checking models.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__CHECK_MODELS_H
#define CVC5__SMT__CHECK_MODELS_H

#include "context/cdlist.h"
#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace theory {
class TheoryModel;
}

namespace smt {

/**
 * This utility is responsible for checking the current model.
 */
class CheckModels : protected EnvObj
{
 public:
  CheckModels(Env& e);
  /**
   * Check model m against the current set of input assertions al.
   *
   * This throws an exception if we fail to verify that m is a proper model
   * given assertion list al based on the model checking policy.
   *
   * @param m           The model to check.
   * @param al          The input assertions.
   * @param hardFailure True have a failed model check should result in an
   *                    InternalError rather than only issue a warning.
   */
  void checkModel(theory::TheoryModel* m,
                  const context::CDList<Node>& al,
                  bool hardFailure);

 private:
  /**
   * Attempt to check a separation logic assertion that could not be evaluated
   * directly against the heap model (e.g. because it contains a magic wand).
   *
   * We pin the heap to the concrete heap model and the free symbols of the
   * assertion to their model values, then ask a subsolver whether the
   * assertion is still satisfiable. Since the pinned heap describes exactly
   * one heap (the model heap), a satisfiable result means the model satisfies
   * the assertion, and an unsatisfiable result means it does not.
   *
   * @param m The model.
   * @param sepHeap The concrete heap model term.
   * @param sepNeq The separation nil equality of the model.
   * @param heapIsGround Whether sepHeap and sepNeq are ground, i.e. whether
   * they describe exactly one heap. If they do not, this declines to check
   * rather than reporting a result it did not establish.
   * @param assertion The assertion to check.
   * @return the Boolean constant true if the model satisfies the assertion,
   * false if it provably does not, or the null node if this could not be
   * determined (e.g. the subsolver returned unknown).
   */
  Node checkSepAssertionWithSubsolver(theory::TheoryModel* m,
                                      TNode sepHeap,
                                      TNode sepNeq,
                                      bool heapIsGround,
                                      TNode assertion);
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
