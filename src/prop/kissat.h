/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper for Kissat SAT Solver.
 *
 * Wrapper for the Kissat SAT solver (for theory of bit-vectors).
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__KISSAT_H
#define CVC5__PROP__KISSAT_H

#ifdef CVC5_USE_KISSAT

#include "prop/sat_solver.h"

extern "C" {
#include <kissat/kissat.h>
}

namespace cvc5::internal {
namespace prop {

class KissatSolver : public SatSolver
{
  friend class SatSolverFactory;

 public:
  ~KissatSolver() override;

  ClauseId addClause(SatClause& clause, bool removable) override;

  ClauseId addXorClause(SatClause& clause, bool rhs, bool removable) override;

  SatVariable newVar(bool isTheoryAtom = false, bool canErase = true) override;

  SatVariable trueVar() override;
  SatVariable falseVar() override;

  SatValue solve() override;
  SatValue solve(long unsigned int&) override;
  SatValue solve(const std::vector<SatLiteral>& assumptions) override;

  void interrupt() override;

  SatValue value(SatLiteral l) override;

  SatValue modelValue(SatLiteral l) override;

  uint32_t getAssertionLevel() const override;

  bool ok() const override;

 private:
  struct Statistics
  {
    IntStat d_numSatCalls;
    IntStat d_numVariables;
    IntStat d_numClauses;
    TimerStat d_solveTime;
    Statistics(StatisticsRegistry& registry, const std::string& prefix);
  };

  /**
   * Private to disallow creation outside of SatSolverFactory.
   * Function init() must be called after creation.
   */
  KissatSolver(StatisticsRegistry& registry, const std::string& name = "");
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
}  // namespace cvc5::internal

#endif  // CVC5_USE_KISSAT
#endif  // CVC5__PROP__KISSAT_H
