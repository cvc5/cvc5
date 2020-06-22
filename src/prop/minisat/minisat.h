/*********************                                                        */
/*! \file minisat.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Liana Hadarean, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** Implementation of the minisat interface for cvc4.
 **/

#pragma once

#include "prop/sat_solver.h"
#include "prop/minisat/simp/SimpSolver.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace prop {

class MinisatSatSolver : public DPLLSatSolverInterface {
public:

  MinisatSatSolver(StatisticsRegistry* registry);
  ~MinisatSatSolver() override;

  static SatVariable     toSatVariable(Minisat::Var var);
  static Minisat::Lit    toMinisatLit(SatLiteral lit);
  static SatLiteral      toSatLiteral(Minisat::Lit lit);
  static SatValue        toSatLiteralValue(Minisat::lbool res);
  static Minisat::lbool  toMinisatlbool(SatValue val);
  //(Commented because not in use) static bool            tobool(SatValue val);

  static void  toMinisatClause(SatClause& clause, Minisat::vec<Minisat::Lit>& minisat_clause);
  static void  toSatClause    (const Minisat::Clause& clause, SatClause& sat_clause);
  void initialize(context::Context* context, TheoryProxy* theoryProxy) override;

  ClauseId addClause(SatClause& clause, bool removable) override;
  ClauseId addXorClause(SatClause& clause, bool rhs, bool removable) override
  {
    Unreachable() << "Minisat does not support native XOR reasoning";
  }

  SatVariable newVar(bool isTheoryAtom,
                     bool preRegister,
                     bool canErase) override;
  SatVariable trueVar() override { return d_minisat->trueVar(); }
  SatVariable falseVar() override { return d_minisat->falseVar(); }

  SatValue solve() override;
  SatValue solve(long unsigned int&) override;

  bool ok() const override;

  void interrupt() override;

  SatValue value(SatLiteral l) override;

  SatValue modelValue(SatLiteral l) override;

  bool properExplanation(SatLiteral lit, SatLiteral expl) const override;

  /** Incremental interface */

  unsigned getAssertionLevel() const override;

  void push() override;

  void pop() override;

  void resetTrail() override;

  void requirePhase(SatLiteral lit) override;

  bool isDecision(SatVariable decn) const override;

 private:

  /** The SatSolver used */
  Minisat::SimpSolver* d_minisat;

  /** Context we will be using to synchronize the sat solver */
  context::Context* d_context;

  void setupOptions();

  class Statistics {
  private:
    StatisticsRegistry* d_registry;
    ReferenceStat<uint64_t> d_statStarts, d_statDecisions;
    ReferenceStat<uint64_t> d_statRndDecisions, d_statPropagations;
    ReferenceStat<uint64_t> d_statConflicts, d_statClausesLiterals;
    ReferenceStat<uint64_t> d_statLearntsLiterals,  d_statMaxLiterals;
    ReferenceStat<uint64_t> d_statTotLiterals;
  public:
    Statistics(StatisticsRegistry* registry);
    ~Statistics();
    void init(Minisat::SimpSolver* d_minisat);
  };/* class MinisatSatSolver::Statistics */
  Statistics d_statistics;

};/* class MinisatSatSolver */

}/* CVC4::prop namespace */
}/* CVC4 namespace */
