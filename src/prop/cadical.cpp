/*********************                                                        */
/*! \file cadical.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Andres Noetzli, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Wrapper for CaDiCaL SAT Solver.
 **
 ** Implementation of the CaDiCaL SAT solver for CVC4 (bitvectors).
 **/

#include "prop/cadical.h"

#ifdef CVC4_USE_CADICAL

#include "base/check.h"

namespace CVC4 {
namespace prop {

using CadicalLit = int;
using CadicalVar = int;

// helper functions
namespace {

SatValue toSatValue(int result)
{
  if (result == 10) return SAT_VALUE_TRUE;
  if (result == 20) return SAT_VALUE_FALSE;
  Assert(result == 0);
  return SAT_VALUE_UNKNOWN;
}

/* Note: CaDiCaL returns lit/-lit for true/false. Older versions returned 1/-1.
 */
SatValue toSatValueLit(int value)
{
  if (value > 0) return SAT_VALUE_TRUE;
  Assert(value < 0);
  return SAT_VALUE_FALSE;
}

CadicalLit toCadicalLit(const SatLiteral lit)
{
  return lit.isNegated() ? -lit.getSatVariable() : lit.getSatVariable();
}

CadicalVar toCadicalVar(SatVariable var) { return var; }

}  // namespace helper functions

CadicalSolver::CadicalSolver(StatisticsRegistry* registry,
                             const std::string& name)
    : d_solver(new CaDiCaL::Solver()),
      // Note: CaDiCaL variables start with index 1 rather than 0 since negated
      //       literals are represented as the negation of the index.
      d_nextVarIdx(1),
      d_statistics(registry, name)
{
}

void CadicalSolver::init()
{
  d_true = newVar();
  d_false = newVar();

  d_solver->set("quiet", 1);  // CaDiCaL is verbose by default
  d_solver->add(toCadicalVar(d_true));
  d_solver->add(0);
  d_solver->add(-toCadicalVar(d_false));
  d_solver->add(0);
}

CadicalSolver::~CadicalSolver() {}

ClauseId CadicalSolver::addClause(SatClause& clause, bool removable)
{
  for (const SatLiteral& lit : clause)
  {
    d_solver->add(toCadicalLit(lit));
  }
  d_solver->add(0);
  ++d_statistics.d_numClauses;
  return ClauseIdError;
}

ClauseId CadicalSolver::addXorClause(SatClause& clause,
                                     bool rhs,
                                     bool removable)
{
  Unreachable() << "CaDiCaL does not support adding XOR clauses.";
}

SatVariable CadicalSolver::newVar(bool isTheoryAtom,
                                  bool preRegister,
                                  bool canErase)
{
  ++d_statistics.d_numVariables;
  return d_nextVarIdx++;
}

SatVariable CadicalSolver::trueVar() { return d_true; }

SatVariable CadicalSolver::falseVar() { return d_false; }

SatValue CadicalSolver::solve()
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveTime);
  SatValue res = toSatValue(d_solver->solve());
  d_okay = (res == SAT_VALUE_TRUE);
  ++d_statistics.d_numSatCalls;
  return res;
}

SatValue CadicalSolver::solve(long unsigned int&)
{
  Unimplemented() << "Setting limits for CaDiCaL not supported yet";
};

SatValue CadicalSolver::solve(const std::vector<SatLiteral>& assumptions)
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveTime);
  for (const SatLiteral& lit : assumptions)
  {
    d_solver->assume(toCadicalLit(lit));
  }
  SatValue res = toSatValue(d_solver->solve());
  d_okay = (res == SAT_VALUE_TRUE);
  ++d_statistics.d_numSatCalls;
  return res;
}

void CadicalSolver::interrupt() { d_solver->terminate(); }

SatValue CadicalSolver::value(SatLiteral l)
{
  Assert(d_okay);
  return toSatValueLit(d_solver->val(toCadicalLit(l)));
}

SatValue CadicalSolver::modelValue(SatLiteral l)
{
  Assert(d_okay);
  return value(l);
}

unsigned CadicalSolver::getAssertionLevel() const
{
  Unreachable() << "CaDiCaL does not support assertion levels.";
}

bool CadicalSolver::ok() const { return d_okay; }

CadicalSolver::Statistics::Statistics(StatisticsRegistry* registry,
                                      const std::string& prefix)
    : d_registry(registry),
      d_numSatCalls("theory::bv::" + prefix + "::cadical::calls_to_solve", 0),
      d_numVariables("theory::bv::" + prefix + "::cadical::variables", 0),
      d_numClauses("theory::bv::" + prefix + "::cadical::clauses", 0),
      d_solveTime("theory::bv::" + prefix + "::cadical::solve_time")
{
  d_registry->registerStat(&d_numSatCalls);
  d_registry->registerStat(&d_numVariables);
  d_registry->registerStat(&d_numClauses);
  d_registry->registerStat(&d_solveTime);
}

CadicalSolver::Statistics::~Statistics() {
  d_registry->unregisterStat(&d_numSatCalls);
  d_registry->unregisterStat(&d_numVariables);
  d_registry->unregisterStat(&d_numClauses);
  d_registry->unregisterStat(&d_solveTime);
}

}  // namespace prop
}  // namespace CVC4

#endif  // CVC4_USE_CADICAL
