/*********************                                                        */
/*! \file lazy_bitblaster.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitblaster for the lazy bv solver.
 **
 ** Bitblaster for the lazy bv solver.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__BITBLAST__LAZY_BITBLASTER_H
#define CVC4__THEORY__BV__BITBLAST__LAZY_BITBLASTER_H

#include "proof/resolution_bitvector_proof.h"
#include "theory/bv/bitblast/bitblaster.h"

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "prop/cnf_stream.h"
#include "prop/registrar.h"
#include "prop/bv_sat_solver_notify.h"
#include "theory/bv/abstraction.h"

namespace CVC4 {
namespace theory {
namespace bv {

class TheoryBV;

class TLazyBitblaster : public TBitblaster<Node>
{
 public:
  void bbTerm(TNode node, Bits& bits) override;
  void bbAtom(TNode node) override;
  Node getBBAtom(TNode atom) const override;
  void storeBBAtom(TNode atom, Node atom_bb) override;
  void storeBBTerm(TNode node, const Bits& bits) override;
  bool hasBBAtom(TNode atom) const override;

  TLazyBitblaster(context::Context* c,
                  TheoryBV* bv,
                  const std::string name = "",
                  bool emptyNotify = false);
  ~TLazyBitblaster();
  /**
   * Pushes the assumption literal associated with node to the SAT
   * solver assumption queue.
   *
   * @param node assumption
   * @param propagate run bcp or not
   *
   * @return false if a conflict detected
   */
  bool assertToSat(TNode node, bool propagate = true);
  bool propagate();
  bool solve();
  prop::SatValue solveWithBudget(unsigned long conflict_budget);
  void getConflict(std::vector<TNode>& conflict);
  void explain(TNode atom, std::vector<TNode>& explanation);
  void setAbstraction(AbstractionModule* abs);

  theory::EqualityStatus getEqualityStatus(TNode a, TNode b);

  /**
   * Adds a constant value for each bit-blasted variable in the model.
   *
   * @param m the model
   * @param fullModel whether to create a "full model," i.e., add
   * constants to equivalence classes that don't already have them
   */
  bool collectModelInfo(TheoryModel* m, bool fullModel);

  typedef TNodeSet::const_iterator vars_iterator;
  vars_iterator beginVars() { return d_variables.begin(); }
  vars_iterator endVars() { return d_variables.end(); }

  /**
   * Creates the bits corresponding to the variable (or non-bv term).
   *
   * @param var
   */
  void makeVariable(TNode var, Bits& bits) override;

  bool isSharedTerm(TNode node);
  uint64_t computeAtomWeight(TNode node, NodeSet& seen);
  /**
   * Deletes SatSolver and CnfCache, but maintains bit-blasting
   * terms cache.
   *
   */
  void clearSolver();

 private:
  typedef std::vector<Node> Bits;
  typedef context::CDList<prop::SatLiteral> AssertionList;
  typedef context::CDHashMap<prop::SatLiteral,
                             std::vector<prop::SatLiteral>,
                             prop::SatLiteralHashFunction>
      ExplanationMap;
  /** This class gets callbacks from minisat on propagations */
  class MinisatNotify : public prop::BVSatSolverNotify
  {
    prop::CnfStream* d_cnf;
    TheoryBV* d_bv;
    TLazyBitblaster* d_lazyBB;

   public:
    MinisatNotify(prop::CnfStream* cnf, TheoryBV* bv, TLazyBitblaster* lbv)
        : d_cnf(cnf), d_bv(bv), d_lazyBB(lbv)
    {
    }

    bool notify(prop::SatLiteral lit) override;
    void notify(prop::SatClause& clause) override;
    void spendResource(ResourceManager::Resource r) override;
    void safePoint(ResourceManager::Resource r) override;
  };

  TheoryBV* d_bv;
  context::Context* d_ctx;

  std::unique_ptr<prop::NullRegistrar> d_nullRegistrar;
  std::unique_ptr<prop::BVSatSolverInterface> d_satSolver;
  std::unique_ptr<prop::BVSatSolverNotify> d_satSolverNotify;

  AssertionList*
      d_assertedAtoms;            /**< context dependent list storing the atoms
                                     currently asserted by the DPLL SAT solver. */
  ExplanationMap* d_explanations; /**< context dependent list of explanations
                                    for the propagated literals. Only used when
                                    bvEagerPropagate option enabled. */
  TNodeSet d_variables;
  TNodeSet d_bbAtoms;
  AbstractionModule* d_abstraction;
  bool d_emptyNotify;

  // The size of the fact queue when we most recently called solve() in the
  // bit-vector SAT solver. This is the level at which we should have
  // a full model in the bv SAT solver.
  context::CDO<int> d_fullModelAssertionLevel;

  void addAtom(TNode atom);
  bool hasValue(TNode a);
  Node getModelFromSatSolver(TNode a, bool fullModel) override;
  prop::SatSolver* getSatSolver() override { return d_satSolver.get(); }

  class Statistics
  {
   public:
    IntStat d_numTermClauses, d_numAtomClauses;
    IntStat d_numTerms, d_numAtoms;
    IntStat d_numExplainedPropagations;
    IntStat d_numBitblastingPropagations;
    TimerStat d_bitblastTimer;
    Statistics(const std::string& name);
    ~Statistics();
  };
  std::string d_name;

 // NOTE: d_statistics is public since d_bitblastTimer needs to be initalized
 //       prior to calling bbAtom. As it is now, the timer can't be initialized
 //       in bbAtom since the method is called recursively and the timer would
 //       be initialized multiple times, which is not allowed.
 public:
  Statistics d_statistics;
};

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
#endif  //  CVC4__THEORY__BV__BITBLAST__LAZY_BITBLASTER_H
