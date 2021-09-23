/******************************************************************************
 * Top contributors (to current version):
 *   Liana Hadarean, Mathias Preiner, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eager bit-blasting solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BV_EAGER_SOLVER_H
#define CVC5__THEORY__BV__BV_EAGER_SOLVER_H

#include "expr/node.h"
#include "theory/bv/bv_solver_layered.h"
#include "theory/theory_model.h"

namespace cvc5 {
namespace theory {
namespace bv {

class EagerBitblaster;
class AigBitblaster;

/**
 * BitblastSolver
 */
class EagerBitblastSolver {
 public:
  EagerBitblastSolver(context::Context* c, theory::bv::BVSolverLayered* bv);
  ~EagerBitblastSolver();
  bool checkSat();
  void assertFormula(TNode formula);

  void turnOffAig();
  bool isInitialized();
  void initialize();
  bool collectModelInfo(theory::TheoryModel* m, bool fullModel);

 private:
  context::CDHashSet<Node> d_assertionSet;
  context::CDHashSet<Node> d_assumptionSet;
  context::Context* d_context;

  /** Bitblasters */
  std::unique_ptr<EagerBitblaster> d_bitblaster;
  std::unique_ptr<AigBitblaster> d_aigBitblaster;
  bool d_useAig;

  BVSolverLayered* d_bv;
};  // class EagerBitblastSolver

}  // namespace bv
}  // namespace theory
}  // namespace cvc5

#endif  // CVC5__THEORY__BV__BV_EAGER_SOLVER_H
