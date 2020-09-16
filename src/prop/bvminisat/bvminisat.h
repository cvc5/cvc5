/*********************                                                        */
/*! \file bvminisat.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** Implementation of the minisat for cvc4 (bitvectors).
 **/

#include "cvc4_private.h"

#pragma once

#include <memory>

#include "context/cdo.h"
#include "prop/bv_sat_solver_notify.h"
#include "prop/bvminisat/simp/SimpSolver.h"
#include "prop/sat_solver.h"
#include "util/resource_manager.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace prop {

class BVMinisatSatSolver : public BVSatSolverInterface,
                           public context::ContextNotifyObj
{
 private:
  class MinisatNotify : public BVMinisat::Notify
  {
    BVSatSolverNotify* d_notify;

   public:
    MinisatNotify(BVSatSolverNotify* notify) : d_notify(notify) {}
    bool notify(BVMinisat::Lit lit) override
    {
      return d_notify->notify(toSatLiteral(lit));
    }
    void notify(BVMinisat::vec<BVMinisat::Lit>& clause) override;
    void spendResource(ResourceManager::Resource r) override
    {
      d_notify->spendResource(r);
    }
    void safePoint(ResourceManager::Resource r) override
    {
      d_notify->safePoint(r);
    }
  };

  std::unique_ptr<BVMinisat::SimpSolver> d_minisat;
  std::unique_ptr<MinisatNotify> d_minisatNotify;

  unsigned d_assertionsCount;
  context::CDO<unsigned> d_assertionsRealCount;
  context::CDO<unsigned> d_lastPropagation;

protected:
 void contextNotifyPop() override;

public:

  BVMinisatSatSolver(StatisticsRegistry* registry, context::Context* mainSatContext, const std::string& name = "");
  virtual ~BVMinisatSatSolver();

  void setNotify(BVSatSolverNotify* notify) override;

  ClauseId addClause(SatClause& clause, bool removable) override;

  ClauseId addXorClause(SatClause& clause, bool rhs, bool removable) override
  {
    Unreachable() << "Minisat does not support native XOR reasoning";
    return ClauseIdError;
  }

  SatValue propagate() override;

  SatVariable newVar(bool isTheoryAtom = false,
                     bool preRegister = false,
                     bool canErase = true) override;

  SatVariable trueVar() override { return d_minisat->trueVar(); }
  SatVariable falseVar() override { return d_minisat->falseVar(); }

  void markUnremovable(SatLiteral lit) override;

  void interrupt() override;

  SatValue solve() override;
  SatValue solve(long unsigned int&) override;
  bool ok() const override;
  void getUnsatCore(SatClause& unsatCore) override;

  SatValue value(SatLiteral l) override;
  SatValue modelValue(SatLiteral l) override;

  void unregisterVar(SatLiteral lit);
  void renewVar(SatLiteral lit, int level = -1);
  unsigned getAssertionLevel() const override;

  // helper methods for converting from the internal Minisat representation

  static SatVariable     toSatVariable(BVMinisat::Var var);
  static BVMinisat::Lit    toMinisatLit(SatLiteral lit);
  static SatLiteral      toSatLiteral(BVMinisat::Lit lit);
  static SatValue toSatLiteralValue(BVMinisat::lbool res);

  static void  toMinisatClause(SatClause& clause, BVMinisat::vec<BVMinisat::Lit>& minisat_clause);
  static void  toSatClause    (const BVMinisat::Clause& clause, SatClause& sat_clause);
  void addMarkerLiteral(SatLiteral lit) override;

  void explain(SatLiteral lit, std::vector<SatLiteral>& explanation) override;

  SatValue assertAssumption(SatLiteral lit, bool propagate) override;

  void popAssumption() override;

 private:
  /* Disable the default constructor. */
  BVMinisatSatSolver() = delete;

  class Statistics {
  public:
    StatisticsRegistry* d_registry;
    ReferenceStat<uint64_t> d_statStarts, d_statDecisions;
    ReferenceStat<uint64_t> d_statRndDecisions, d_statPropagations;
    ReferenceStat<uint64_t> d_statConflicts, d_statClausesLiterals;
    ReferenceStat<uint64_t> d_statLearntsLiterals,  d_statMaxLiterals;
    ReferenceStat<uint64_t> d_statTotLiterals;
    ReferenceStat<int> d_statEliminatedVars;
    IntStat d_statCallsToSolve;
    TimerStat d_statSolveTime;
    bool d_registerStats;
    Statistics(StatisticsRegistry* registry, const std::string& prefix);
    ~Statistics();
    void init(BVMinisat::SimpSolver* minisat);
  };

  Statistics d_statistics;
};

} /* CVC4::prop namespace */
} /* CVC4 namespace */
