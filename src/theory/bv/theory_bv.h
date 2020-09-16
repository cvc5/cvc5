/*********************                                                        */
/*! \file theory_bv.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__THEORY_BV_H
#define CVC4__THEORY__BV__THEORY_BV_H

#include <unordered_map>

#include "theory/bv/theory_bv_rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace bv {

class BVSolver;

class TheoryBV : public Theory
{
  /* BVSolverLazy accesses methods from theory in a way that is deprecated and
   * will be removed in the future. For now we allow direct access. */
  friend class BVSolverLazy;

 public:
  TheoryBV(context::Context* c,
           context::UserContext* u,
           OutputChannel& out,
           Valuation valuation,
           const LogicInfo& logicInfo,
           ProofNodeManager* pnm = nullptr,
           std::string name = "");

  ~TheoryBV();

  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;

  /**
   * Returns true if we need an equality engine. If so, we initialize the
   * information regarding how it should be setup. For details, see the
   * documentation in Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi) override;

  void finishInit() override;

  TrustNode expandDefinition(Node node) override;

  void preRegisterTerm(TNode n) override;

  bool preCheck(Effort e) override;

  bool needsCheckLastEffort() override;

  void propagate(Effort e) override;

  TrustNode explain(TNode n) override;

  /** Collect model values in m based on the relevant terms given by termSet */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  std::string identify() const override { return std::string("TheoryBV"); }

  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions) override;

  TrustNode ppRewrite(TNode t) override;

  void ppStaticLearn(TNode in, NodeBuilder<>& learned) override;

  void presolve() override;

  /** Called by abstraction preprocessing pass. */
  bool applyAbstraction(const std::vector<Node>& assertions,
                        std::vector<Node>& new_assertions);

 private:
  void notifySharedTerm(TNode t) override;

  /**
   * Return the UF symbol corresponding to division-by-zero for this particular
   * bit-width.
   * @param k should be UREM or UDIV
   * @param width bit-width
   */
  Node getUFDivByZero(Kind k, unsigned width);

  /** Internal BV solver. */
  std::unique_ptr<BVSolver> d_internal;

  /**
   * Maps from bit-vector width to division-by-zero uninterpreted
   * function symbols.
   */
  std::unordered_map<unsigned, Node> d_ufDivByZero;
  std::unordered_map<unsigned, Node> d_ufRemByZero;

  /** The theory rewriter for this theory. */
  TheoryBVRewriter d_rewriter;

  /** A (default) theory state object */
  TheoryState d_state;

  /** A (default) theory inference manager. */
  TheoryInferenceManager d_inferMgr;

}; /* class TheoryBV */

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BV__THEORY_BV_H */
