/*********************                                                        */
/*! \file kissat.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Wrapper for Kissat SAT Solver.
 **
 ** Wrapper for the Kissat SAT solver (for theory of bit-vectors).
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROP__KISSAT_H
#define CVC4__PROP__KISSAT_H

#ifdef CVC4_USE_KISSAT

#include "prop/sat_solver.h"

extern "C" {
#include <kissat/kissat.h>
}

namespace CVC4 {
namespace prop {

class KissatSolver : public SatSolver
{
  friend class SatSolverFactory;

 public:
  ~KissatSolver() override;

  ClauseId addClause(SatClause& clause, bool removable) override;

  ClauseId addXorClause(SatClause& clause, bool rhs, bool removable) override;

  SatVariable newVar(bool isTheoryAtom = false,
                     bool preRegister = false,
                     bool canErase = true) override;

  SatVariable trueVar() override;
  SatVariable falseVar() override;

  SatValue solve() override;
  SatValue solve(long unsigned int&) override;
  SatValue solve(const std::vector<SatLiteral>& assumptions) override;

  void interrupt() override;

  SatValue value(SatLiteral l) override;

  SatValue modelValue(SatLiteral l) override;

  unsigned getAssertionLevel() const override;

  bool ok() const override;

 private:
  struct Statistics
  {
    StatisticsRegistry* d_registry;
    IntStat d_numSatCalls;
    IntStat d_numVariables;
    IntStat d_numClauses;
    TimerStat d_solveTime;
    Statistics(StatisticsRegistry* registry, const std::string& prefix);
    ~Statistics();
  };

  /**
   * Private to disallow creation outside of SatSolverFactory.
   * Function init() must be called after creation.
   */
  KissatSolver(StatisticsRegistry* registry, const std::string& name = "");
  /**
   * Initialize SAT solver instance.
   * Note: Split out to not call virtual functions in constructor.
   */
  void init();

  kissat* d_solver;

  unsigned d_nextVarIdx;
  bool d_okay;
  SatVariable d_true;
  SatVariable d_false;

  Statistics d_statistics;
};

}  // namespace prop
}  // namespace CVC4

#endif  // CVC4_USE_KISSAT
#endif  // CVC4__PROP__KISSAT_H
