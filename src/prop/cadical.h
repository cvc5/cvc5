/*********************                                                        */
/*! \file cadical.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Wrapper for CaDiCaL SAT Solver.
 **
 ** Implementation of the CaDiCaL SAT solver for CVC4 (bitvectors).
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROP__CADICAL_H
#define CVC4__PROP__CADICAL_H

#ifdef CVC4_USE_CADICAL

#include "prop/sat_solver.h"

#include <cadical.hpp>

namespace CVC4 {
namespace prop {

class CadicalSolver : public SatSolver
{
  friend class SatSolverFactory;

 public:
  ~CadicalSolver() override;

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
  /**
   * Private to disallow creation outside of SatSolverFactory.
   * Function init() must be called after creation.
   */
  CadicalSolver(StatisticsRegistry* registry, const std::string& name = "");
  /**
   * Initialize SAT solver instance.
   * Note: Split out to not call virtual functions in constructor.
   */
  void init();

  std::unique_ptr<CaDiCaL::Solver> d_solver;

  unsigned d_nextVarIdx;
  bool d_okay;
  SatVariable d_true;
  SatVariable d_false;

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

  Statistics d_statistics;
};

}  // namespace prop
}  // namespace CVC4

#endif  // CVC4_USE_CADICAL
#endif  // CVC4__PROP__CADICAL_H
