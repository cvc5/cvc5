/*********************                                                        */
/*! \file bv_solver_simple.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Simple bit-blast solver
 **
 ** Simple bit-blast solver that sends bit-blast lemmas directly to MiniSat.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__BV_SOLVER_SIMPLE_H
#define CVC4__THEORY__BV__BV_SOLVER_SIMPLE_H

#include <unordered_map>

#include "theory/bv/bv_solver.h"

namespace CVC4 {

namespace theory {
namespace bv {

class BBSimple;

/**
 * Simple bit-blasting solver that sends bit-blasting lemmas directly to the
 * internal MiniSat. It is also ablo to handle atoms of kind
 * BITVECTOR_EAGER_ATOM.
 *
 * Sends lemmas atom <=> bb(atom) to MiniSat on preNotifyFact().
 */
class BVSolverSimple : public BVSolver
{
 public:
  BVSolverSimple(TheoryState& state, TheoryInferenceManager& inferMgr);
  ~BVSolverSimple() = default;

  void preRegisterTerm(TNode n) override {}

  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;

  std::string identify() const override { return "BVSolverSimple"; };

  Theory::PPAssertStatus ppAssert(TNode in,
                                  SubstitutionMap& outSubstitutions) override
  {
    return Theory::PPAssertStatus::PP_ASSERT_STATUS_UNSOLVED;
  }

  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

 private:
  /**
   * Sends a bit-blasting lemma fact <=> d_bitblaster.bbAtom(fact) to the
   * inference manager.
   */
  void addBBLemma(TNode fact);

  /** Bit-blaster used to bit-blast atoms/terms. */
  std::unique_ptr<BBSimple> d_bitblaster;
};

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

#endif
