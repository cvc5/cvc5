/******************************************************************************
 * Top contributors (to current version):
 *   Liana Hadarean, Mathias Preiner, Alex Ozdemir
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
 * Implementation of the cryptominisat for cvc5 (bit-vectors).
 */

#include "prop/cryptominisat.h"

#ifdef CVC5_USE_CRYPTOMINISAT

#include "base/check.h"
#include "util/statistics_registry.h"

#include <cryptominisat5/cryptominisat.h>

namespace cvc5 {
namespace prop {

using CMSatVar = unsigned;

// helper functions
namespace {

CMSat::Lit toInternalLit(SatLiteral lit)
{
  if (lit == undefSatLiteral)
  {
    return CMSat::lit_Undef;
  }
  return CMSat::Lit(lit.getSatVariable(), lit.isNegated());
}

SatLiteral toSatLiteral(CMSat::Lit lit)
{
  if (lit == CMSat::lit_Undef)
  {
    return undefSatLiteral;
  }
  return SatLiteral(lit.var(), lit.sign());
}

SatValue toSatLiteralValue(CMSat::lbool res)
{
  if (res == CMSat::l_True) return SAT_VALUE_TRUE;
  if (res == CMSat::l_Undef) return SAT_VALUE_UNKNOWN;
  Assert(res == CMSat::l_False);
  return SAT_VALUE_FALSE;
}

void toInternalClause(SatClause& clause,
                      std::vector<CMSat::Lit>& internal_clause)
{
  for (unsigned i = 0; i < clause.size(); ++i)
  {
    internal_clause.push_back(toInternalLit(clause[i]));
  }
  Assert(clause.size() == internal_clause.size());
}

}  // helper functions

CryptoMinisatSolver::CryptoMinisatSolver(StatisticsRegistry& registry,
                                         const std::string& name)
    : d_solver(new CMSat::SATSolver()),
      d_numVariables(0),
      d_okay(true),
      d_statistics(registry, name)
{
}

void CryptoMinisatSolver::init()
{
  d_true = newVar();
  d_false = newVar();

  std::vector<CMSat::Lit> clause(1);
  clause[0] = CMSat::Lit(d_true, false);
  d_solver->add_clause(clause);

  clause[0] = CMSat::Lit(d_false, true);
  d_solver->add_clause(clause);
}

CryptoMinisatSolver::~CryptoMinisatSolver() {}

ClauseId CryptoMinisatSolver::addXorClause(SatClause& clause,
                                           bool rhs,
                                           bool removable)
{
  Debug("sat::cryptominisat") << "Add xor clause " << clause <<" = " << rhs << "\n";

  if (!d_okay) {
    Debug("sat::cryptominisat") << "Solver unsat: not adding clause.\n";
    return ClauseIdError;
  }

  ++(d_statistics.d_xorClausesAdded);

  // ensure all sat literals have positive polarity by pushing
  // the negation on the result
  std::vector<CMSatVar> xor_clause;
  for (unsigned i = 0; i < clause.size(); ++i) {
    xor_clause.push_back(toInternalLit(clause[i]).var());
    rhs ^= clause[i].isNegated();
  }
  bool res = d_solver->add_xor_clause(xor_clause, rhs);
  d_okay &= res;
  return ClauseIdError;
}

ClauseId CryptoMinisatSolver::addClause(SatClause& clause, bool removable){
  Debug("sat::cryptominisat") << "Add clause " << clause <<"\n";

  if (!d_okay) {
    Debug("sat::cryptominisat") << "Solver unsat: not adding clause.\n";
    return ClauseIdError;
  }

  ++(d_statistics.d_clausesAdded);

  std::vector<CMSat::Lit> internal_clause;
  toInternalClause(clause, internal_clause);
  bool nowOkay = d_solver->add_clause(internal_clause);

  ClauseId freshId;
  freshId = ClauseIdError;

  d_okay &= nowOkay;
  return freshId;
}

bool CryptoMinisatSolver::ok() const { return d_okay; }

SatVariable  CryptoMinisatSolver::newVar(bool isTheoryAtom, bool preRegister, bool canErase){
  d_solver->new_var();
  ++d_numVariables;
  Assert(d_numVariables == d_solver->nVars());
  return d_numVariables - 1;
}

SatVariable CryptoMinisatSolver::trueVar() {
  return d_true;
}

SatVariable CryptoMinisatSolver::falseVar() {
  return d_false;
}

void CryptoMinisatSolver::markUnremovable(SatLiteral lit) {
  // cryptominisat supports dynamically adding back variables (?)
  // so this is a no-op
  return;
}

void CryptoMinisatSolver::interrupt(){
  d_solver->interrupt_asap();
}

SatValue CryptoMinisatSolver::solve(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveTime);
  ++d_statistics.d_statCallsToSolve;
  return toSatLiteralValue(d_solver->solve());
}

SatValue CryptoMinisatSolver::solve(long unsigned int& resource) {
  // CMSat::SalverConf conf = d_solver->getConf();
  Unreachable() << "Not sure how to set different limits for calls to solve in "
                   "Cryptominisat";
  return solve();
}

SatValue CryptoMinisatSolver::solve(const std::vector<SatLiteral>& assumptions)
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveTime);
  std::vector<CMSat::Lit> assumpts;
  for (const SatLiteral& lit : assumptions)
  {
    assumpts.push_back(toInternalLit(lit));
  }
  ++d_statistics.d_statCallsToSolve;
  return toSatLiteralValue(d_solver->solve(&assumpts));
}

void CryptoMinisatSolver::getUnsatAssumptions(
    std::vector<SatLiteral>& assumptions)
{
  for (const CMSat::Lit& lit : d_solver->get_conflict())
  {
    assumptions.push_back(toSatLiteral(~lit));
  }
}

SatValue CryptoMinisatSolver::value(SatLiteral l){
  const std::vector<CMSat::lbool> model = d_solver->get_model();
  CMSatVar var = l.getSatVariable();
  Assert(var < model.size());
  CMSat::lbool value = model[var];
  return toSatLiteralValue(value);
}

SatValue CryptoMinisatSolver::modelValue(SatLiteral l) { return value(l); }

unsigned CryptoMinisatSolver::getAssertionLevel() const {
  Unreachable() << "No interface to get assertion level in Cryptominisat";
  return -1;
}

// Satistics for CryptoMinisatSolver

CryptoMinisatSolver::Statistics::Statistics(StatisticsRegistry& registry,
                                            const std::string& prefix)
    : d_statCallsToSolve(registry.registerInt(prefix + "cryptominisat::calls_to_solve")),
      d_xorClausesAdded(registry.registerInt(prefix + "cryptominisat::xor_clauses")),
      d_clausesAdded(registry.registerInt(prefix + "cryptominisat::clauses")),
      d_solveTime(registry.registerTimer(prefix + "cryptominisat::solve_time"))
{
}

}  // namespace prop
}  // namespace cvc5
#endif
