/*********************                                                        */
/*! \file bvminisat.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors:
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2014  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** Implementation of the minisat for cvc4 (bitvectors).
 **/

#include "cvc4_private.h"

#pragma once

#include "context/cdo.h"
#include "proof/clause_id.h"
#include "prop/bvminisat/simp/SimpSolver.h"
#include "prop/sat_solver.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace prop {

class BVMinisatSatSolver : public BVSatSolverInterface, public context::ContextNotifyObj {

private:

  class MinisatNotify : public BVMinisat::Notify {
    BVSatSolverInterface::Notify* d_notify;
  public:
    MinisatNotify(BVSatSolverInterface::Notify* notify)
    : d_notify(notify)
    {}
    bool notify(BVMinisat::Lit lit) {
      return d_notify->notify(toSatLiteral(lit));
    }
    void notify(BVMinisat::vec<BVMinisat::Lit>& clause) {
      SatClause satClause;
      for (int i = 0; i < clause.size(); ++i) {
        satClause.push_back(toSatLiteral(clause[i])); 
      }
      d_notify->notify(satClause);
    }

    void spendResource(unsigned ammount) {
      d_notify->spendResource(ammount);
    }
    void safePoint(unsigned ammount) {
      d_notify->safePoint(ammount);
    }
  };

  BVMinisat::SimpSolver* d_minisat;
  MinisatNotify* d_minisatNotify;

  unsigned d_assertionsCount;
  context::CDO<unsigned> d_assertionsRealCount;
  context::CDO<unsigned> d_lastPropagation;

protected:

  void contextNotifyPop();

public:

  BVMinisatSatSolver(StatisticsRegistry* registry, context::Context* mainSatContext, const std::string& name = "");
  virtual ~BVMinisatSatSolver();

  void setNotify(Notify* notify);

  ClauseId addClause(SatClause& clause, bool removable);

  ClauseId addXorClause(SatClause& clause, bool rhs, bool removable) {
    Unreachable("Minisat does not support native XOR reasoning");
  }
  
  SatValue propagate();

  SatVariable newVar(bool isTheoryAtom = false, bool preRegister = false, bool canErase = true);

  SatVariable trueVar() { return d_minisat->trueVar(); }
  SatVariable falseVar() { return d_minisat->falseVar(); }

  void markUnremovable(SatLiteral lit);

  void interrupt();

  SatValue solve();
  SatValue solve(long unsigned int&);
  bool ok() const; 
  void getUnsatCore(SatClause& unsatCore);

  SatValue value(SatLiteral l);
  SatValue modelValue(SatLiteral l);

  void unregisterVar(SatLiteral lit);
  void renewVar(SatLiteral lit, int level = -1);
  unsigned getAssertionLevel() const;


  // helper methods for converting from the internal Minisat representation

  static SatVariable     toSatVariable(BVMinisat::Var var);
  static BVMinisat::Lit    toMinisatLit(SatLiteral lit);
  static SatLiteral      toSatLiteral(BVMinisat::Lit lit);
  static SatValue toSatLiteralValue(BVMinisat::lbool res);

  static void  toMinisatClause(SatClause& clause, BVMinisat::vec<BVMinisat::Lit>& minisat_clause);
  static void  toSatClause    (const BVMinisat::Clause& clause, SatClause& sat_clause);
  void addMarkerLiteral(SatLiteral lit);

  void explain(SatLiteral lit, std::vector<SatLiteral>& explanation);

  SatValue assertAssumption(SatLiteral lit, bool propagate);

  void popAssumption();
  
  void setProofLog( BitVectorProof * bvp );

private:
  /* Disable the default constructor. */
  BVMinisatSatSolver() CVC4_UNDEFINED;

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
    BackedStat<double> d_statSolveTime;
    bool d_registerStats;
    Statistics(StatisticsRegistry* registry, const std::string& prefix);
    ~Statistics();
    void init(BVMinisat::SimpSolver* minisat);
  };

  Statistics d_statistics;
};

} /* CVC4::prop namespace */
} /* CVC4 namespace */
