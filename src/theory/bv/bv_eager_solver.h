/*********************                                                        */
/*! \file bv_eager_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Eager bit-blasting solver.
 **
 ** Eager bit-blasting solver.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__BV_EAGER_SOLVER_H
#define CVC4__THEORY__BV__BV_EAGER_SOLVER_H

#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "proof/resolution_bitvector_proof.h"
#include "theory/bv/theory_bv.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {
namespace bv {

class EagerBitblaster;
class AigBitblaster;

/**
 * BitblastSolver
 */
class EagerBitblastSolver {
 public:
  EagerBitblastSolver(context::Context* c, theory::bv::TheoryBV* bv);
  ~EagerBitblastSolver();
  bool checkSat();
  void assertFormula(TNode formula);

  void turnOffAig();
  bool isInitialized();
  void initialize();
  bool collectModelInfo(theory::TheoryModel* m, bool fullModel);
  void setProofLog(proof::BitVectorProof* bvp);

 private:
  context::CDHashSet<Node, NodeHashFunction> d_assertionSet;
  context::CDHashSet<Node, NodeHashFunction> d_assumptionSet;
  context::Context* d_context;

  /** Bitblasters */
  std::unique_ptr<EagerBitblaster> d_bitblaster;
  std::unique_ptr<AigBitblaster> d_aigBitblaster;
  bool d_useAig;

  TheoryBV* d_bv;
  proof::BitVectorProof* d_bvp;
};  // class EagerBitblastSolver

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

#endif  // CVC4__THEORY__BV__BV_EAGER_SOLVER_H
