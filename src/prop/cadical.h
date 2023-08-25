/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper for CaDiCaL SAT Solver.
 *
 * Implementation of the CaDiCaL SAT solver for cvc5 (bit-vectors).
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__CADICAL_H
#define CVC5__PROP__CADICAL_H

#include "prop/sat_solver.h"

#include <cadical.hpp>

namespace cvc5::internal {
namespace prop {

class CadicalSolver : public SatSolver
{
  friend class SatSolverFactory;

 public:
  ~CadicalSolver() override;

  ClauseId addClause(SatClause& clause, bool removable) override;

  ClauseId addXorClause(SatClause& clause, bool rhs, bool removable) override;

  SatVariable newVar(bool isTheoryAtom = false, bool canErase = true) override;

  SatVariable trueVar() override;

  SatVariable falseVar() override;

  SatValue solve() override;
  SatValue solve(long unsigned int&) override;
  SatValue solve(const std::vector<SatLiteral>& assumptions) override;
  bool setPropagateOnly() override;
  void getUnsatAssumptions(std::vector<SatLiteral>& assumptions) override;

  void interrupt() override;

  SatValue value(SatLiteral l) override;

  SatValue modelValue(SatLiteral l) override;

  uint32_t getAssertionLevel() const override;

  bool ok() const override;

 private:
  /**
   * Private to disallow creation outside of SatSolverFactory.
   * Function init() must be called after creation.
   */
  CadicalSolver(StatisticsRegistry& registry, const std::string& name = "");
  /**
   * Initialize SAT solver instance.
   * Note: Split out to not call virtual functions in constructor.
   */
  void init();

  /**
   * Set resource limit.
   */
  void setResourceLimit(ResourceManager* resmgr);

  std::unique_ptr<CaDiCaL::Solver> d_solver;
  std::unique_ptr<CaDiCaL::Terminator> d_terminator;

  /**
   * Stores the current set of assumptions provided via solve() and is used to
   * query the solver if a given assumption is false.
   */
  std::vector<SatLiteral> d_assumptions;

  unsigned d_nextVarIdx;
  bool d_inSatMode;
  SatVariable d_true;
  SatVariable d_false;

  struct Statistics
  {
    IntStat d_numSatCalls;
    IntStat d_numVariables;
    IntStat d_numClauses;
    TimerStat d_solveTime;
    Statistics(StatisticsRegistry& registry, const std::string& prefix);
  };

  Statistics d_statistics;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif  // CVC5__PROP__CADICAL_H
