/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Liana Hadarean, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SAT Solver.
 *
 * Implementation of the cryptominisat sat solver for cvc5 (bit-vectors).
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__CRYPTOMINISAT_H
#define CVC5__PROP__CRYPTOMINISAT_H

#ifdef CVC5_USE_CRYPTOMINISAT

#include "prop/sat_solver.h"

// Cryptominisat has name clashes with the other Minisat implementations since
// the Minisat implementations export var_Undef, l_True, ... as macro whereas
// Cryptominisat uses static const. In order to avoid these conflicts we
// forward declare CMSat::SATSolver and include the cryptominisat header only
// in cryptominisat.cpp.
namespace CMSat {
  class SATSolver;
}

namespace cvc5 {
namespace prop {

class CryptoMinisatSolver : public SatSolver
{
  friend class SatSolverFactory;

 public:
  ~CryptoMinisatSolver() override;

  ClauseId addClause(SatClause& clause, bool removable) override;
  ClauseId addXorClause(SatClause& clause, bool rhs, bool removable) override;

  bool nativeXor() override { return true; }

  SatVariable newVar(bool isTheoryAtom = false,
                     bool preRegister = false,
                     bool canErase = true) override;

  SatVariable trueVar() override;
  SatVariable falseVar() override;

  void markUnremovable(SatLiteral lit);

  void interrupt() override;

  SatValue solve() override;
  SatValue solve(long unsigned int&) override;
  SatValue solve(const std::vector<SatLiteral>& assumptions) override;
  void getUnsatAssumptions(std::vector<SatLiteral>& assumptions) override;

  bool ok() const override;
  SatValue value(SatLiteral l) override;
  SatValue modelValue(SatLiteral l) override;

  unsigned getAssertionLevel() const override;

 private:
  class Statistics
  {
   public:
    IntStat d_statCallsToSolve;
    IntStat d_xorClausesAdded;
    IntStat d_clausesAdded;
    TimerStat d_solveTime;
    Statistics(StatisticsRegistry& registry, const std::string& prefix);
  };

  /**
   * Private to disallow creation outside of SatSolverFactory.
   * Function init() must be called after creation.
   */
  CryptoMinisatSolver(StatisticsRegistry& registry,
                      const std::string& name = "");
  /**
   * Initialize SAT solver instance.
   * Note: Split out to not call virtual functions in constructor.
   */
  void init();

  std::unique_ptr<CMSat::SATSolver> d_solver;
  unsigned d_numVariables;
  bool d_okay;
  SatVariable d_true;
  SatVariable d_false;

  Statistics d_statistics;
};

}  // namespace prop
}  // namespace cvc5

#endif  // CVC5_USE_CRYPTOMINISAT
#endif  // CVC5__PROP__CRYPTOMINISAT_H
