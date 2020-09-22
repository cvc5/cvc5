/*********************                                                        */
/*! \file bvminisat.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** Implementation of the minisat for cvc4 (bitvectors).
 **/

#include "prop/bvminisat/bvminisat.h"

#include "prop/bvminisat/simp/SimpSolver.h"
#include "proof/clause_id.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace prop {

BVMinisatSatSolver::BVMinisatSatSolver(StatisticsRegistry* registry, context::Context* mainSatContext, const std::string& name)
: context::ContextNotifyObj(mainSatContext, false),
  d_minisat(new BVMinisat::SimpSolver(mainSatContext)),
  d_minisatNotify(nullptr),
  d_assertionsCount(0),
  d_assertionsRealCount(mainSatContext, 0),
  d_lastPropagation(mainSatContext, 0),
  d_statistics(registry, name)
{
  d_statistics.init(d_minisat.get());
}


BVMinisatSatSolver::~BVMinisatSatSolver() {
}

void BVMinisatSatSolver::MinisatNotify::notify(
    BVMinisat::vec<BVMinisat::Lit>& clause)
{
  SatClause satClause;
  for (unsigned i = 0, n = clause.size(); i < n; ++i)
  {
    satClause.push_back(toSatLiteral(clause[i]));
  }
  d_notify->notify(satClause);
}

void BVMinisatSatSolver::setNotify(BVSatSolverNotify* notify) {
  d_minisatNotify.reset(new MinisatNotify(notify));
  d_minisat->setNotify(d_minisatNotify.get());
}

ClauseId BVMinisatSatSolver::addClause(SatClause& clause,
                                       bool removable) {
  Debug("sat::minisat") << "Add clause " << clause <<"\n";
  BVMinisat::vec<BVMinisat::Lit> minisat_clause;
  toMinisatClause(clause, minisat_clause);
  // for(unsigned i = 0; i < minisat_clause.size(); ++i) {
  //   d_minisat->setFrozen(BVMinisat::var(minisat_clause[i]), true);
  // }
  ClauseId clause_id = ClauseIdError;
  d_minisat->addClause(minisat_clause, clause_id);
  return clause_id;
}

SatValue BVMinisatSatSolver::propagate() {
  return toSatLiteralValue(d_minisat->propagateAssumptions());
}

void BVMinisatSatSolver::addMarkerLiteral(SatLiteral lit) {
  d_minisat->addMarkerLiteral(BVMinisat::var(toMinisatLit(lit)));
  markUnremovable(lit);
}

void BVMinisatSatSolver::explain(SatLiteral lit, std::vector<SatLiteral>& explanation) {
  std::vector<BVMinisat::Lit> minisat_explanation;
  d_minisat->explain(toMinisatLit(lit), minisat_explanation);
  for (unsigned i = 0; i < minisat_explanation.size(); ++i) {
    explanation.push_back(toSatLiteral(minisat_explanation[i]));
  }
}

SatValue BVMinisatSatSolver::assertAssumption(SatLiteral lit, bool propagate) {
  d_assertionsCount ++;
  d_assertionsRealCount = d_assertionsRealCount + 1;
  return toSatLiteralValue(d_minisat->assertAssumption(toMinisatLit(lit), propagate));
}

void BVMinisatSatSolver::contextNotifyPop() {
  while (d_assertionsCount > d_assertionsRealCount) {
    popAssumption();
    d_assertionsCount --;
  }
}

void BVMinisatSatSolver::popAssumption() {
  d_minisat->popAssumption();
}

SatVariable BVMinisatSatSolver::newVar(bool isTheoryAtom, bool preRegister, bool canErase){
  return d_minisat->newVar(true, true, !canErase);
}

void BVMinisatSatSolver::markUnremovable(SatLiteral lit){
  d_minisat->setFrozen(BVMinisat::var(toMinisatLit(lit)), true);
}


void BVMinisatSatSolver::interrupt(){
  d_minisat->interrupt();
}

SatValue BVMinisatSatSolver::solve()
{
  TimerStat::CodeTimer solveTimer(d_statistics.d_statSolveTime);
  ++d_statistics.d_statCallsToSolve;
  return toSatLiteralValue(d_minisat->solve());
}

SatValue BVMinisatSatSolver::solve(long unsigned int& resource){
  Trace("limit") << "MinisatSatSolver::solve(): have limit of " << resource << " conflicts" << std::endl;
  TimerStat::CodeTimer solveTimer(d_statistics.d_statSolveTime);
  ++d_statistics.d_statCallsToSolve;
  if(resource == 0) {
    d_minisat->budgetOff();
  } else {
    d_minisat->setConfBudget(resource);
  }
  //  BVMinisat::vec<BVMinisat::Lit> empty;
  unsigned long conflictsBefore = d_minisat->conflicts;
  SatValue result = toSatLiteralValue(d_minisat->solveLimited());
  d_minisat->clearInterrupt();
  resource = d_minisat->conflicts - conflictsBefore;
  Trace("limit") << "<MinisatSatSolver::solve(): it took " << resource << " conflicts" << std::endl;
  return result;
}

bool BVMinisatSatSolver::ok() const { return d_minisat->okay(); }

void BVMinisatSatSolver::getUnsatCore(SatClause& unsatCore) {
  // TODO add assertion to check the call was after an unsat call
  for (int i = 0; i < d_minisat->conflict.size(); ++i) {
    unsatCore.push_back(toSatLiteral(d_minisat->conflict[i]));
  }
}

SatValue BVMinisatSatSolver::value(SatLiteral l){
  return toSatLiteralValue(d_minisat->value(toMinisatLit(l)));
}

SatValue BVMinisatSatSolver::modelValue(SatLiteral l){
  return toSatLiteralValue(d_minisat->modelValue(toMinisatLit(l)));
}

void BVMinisatSatSolver::unregisterVar(SatLiteral lit) {
  // this should only be called when user context is implemented
  // in the BVSatSolver
  Unreachable();
}

void BVMinisatSatSolver::renewVar(SatLiteral lit, int level) {
  // this should only be called when user context is implemented
  // in the BVSatSolver

  Unreachable();
}

unsigned BVMinisatSatSolver::getAssertionLevel() const {
  // we have no user context implemented so far
  return 0;
}

// converting from internal Minisat representation

SatVariable BVMinisatSatSolver::toSatVariable(BVMinisat::Var var) {
  if (var == var_Undef) {
    return undefSatVariable;
  }
  return SatVariable(var);
}

BVMinisat::Lit BVMinisatSatSolver::toMinisatLit(SatLiteral lit) {
  if (lit == undefSatLiteral) {
    return BVMinisat::lit_Undef;
  }
  return BVMinisat::mkLit(lit.getSatVariable(), lit.isNegated());
}

SatLiteral BVMinisatSatSolver::toSatLiteral(BVMinisat::Lit lit) {
  if (lit == BVMinisat::lit_Undef) {
    return undefSatLiteral;
  }

  return SatLiteral(SatVariable(BVMinisat::var(lit)),
                    BVMinisat::sign(lit));
}

SatValue BVMinisatSatSolver::toSatLiteralValue(BVMinisat::lbool res) {
  if(res == (BVMinisat::lbool((uint8_t)0))) return SAT_VALUE_TRUE;
  if(res == (BVMinisat::lbool((uint8_t)2))) return SAT_VALUE_UNKNOWN;
  Assert(res == (BVMinisat::lbool((uint8_t)1)));
  return SAT_VALUE_FALSE;
}

void BVMinisatSatSolver::toMinisatClause(SatClause& clause,
                                           BVMinisat::vec<BVMinisat::Lit>& minisat_clause) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    minisat_clause.push(toMinisatLit(clause[i]));
  }
  Assert(clause.size() == (unsigned)minisat_clause.size());
}

void BVMinisatSatSolver::toSatClause(const BVMinisat::Clause& clause,
                                     SatClause& sat_clause) {
  for (int i = 0; i < clause.size(); ++i) {
    sat_clause.push_back(toSatLiteral(clause[i]));
  }
  Assert((unsigned)clause.size() == sat_clause.size());
}


// Satistics for BVMinisatSatSolver

BVMinisatSatSolver::Statistics::Statistics(StatisticsRegistry* registry,
                                           const std::string& prefix)
    : d_registry(registry),
      d_statStarts(prefix + "::bvminisat::starts"),
      d_statDecisions(prefix + "::bvminisat::decisions"),
      d_statRndDecisions(prefix + "::bvminisat::rnd_decisions"),
      d_statPropagations(prefix + "::bvminisat::propagations"),
      d_statConflicts(prefix + "::bvminisat::conflicts"),
      d_statClausesLiterals(prefix + "::bvminisat::clauses_literals"),
      d_statLearntsLiterals(prefix + "::bvminisat::learnts_literals"),
      d_statMaxLiterals(prefix + "::bvminisat::max_literals"),
      d_statTotLiterals(prefix + "::bvminisat::tot_literals"),
      d_statEliminatedVars(prefix + "::bvminisat::eliminated_vars"),
      d_statCallsToSolve(prefix + "::bvminisat::calls_to_solve", 0),
      d_statSolveTime(prefix + "::bvminisat::solve_time"),
      d_registerStats(!prefix.empty())
{
  if (!d_registerStats)
  {
    return;
  }

  d_registry->registerStat(&d_statStarts);
  d_registry->registerStat(&d_statDecisions);
  d_registry->registerStat(&d_statRndDecisions);
  d_registry->registerStat(&d_statPropagations);
  d_registry->registerStat(&d_statConflicts);
  d_registry->registerStat(&d_statClausesLiterals);
  d_registry->registerStat(&d_statLearntsLiterals);
  d_registry->registerStat(&d_statMaxLiterals);
  d_registry->registerStat(&d_statTotLiterals);
  d_registry->registerStat(&d_statEliminatedVars);
  d_registry->registerStat(&d_statCallsToSolve);
  d_registry->registerStat(&d_statSolveTime);
}

BVMinisatSatSolver::Statistics::~Statistics() {
  if (!d_registerStats){
    return;
  }
  d_registry->unregisterStat(&d_statStarts);
  d_registry->unregisterStat(&d_statDecisions);
  d_registry->unregisterStat(&d_statRndDecisions);
  d_registry->unregisterStat(&d_statPropagations);
  d_registry->unregisterStat(&d_statConflicts);
  d_registry->unregisterStat(&d_statClausesLiterals);
  d_registry->unregisterStat(&d_statLearntsLiterals);
  d_registry->unregisterStat(&d_statMaxLiterals);
  d_registry->unregisterStat(&d_statTotLiterals);
  d_registry->unregisterStat(&d_statEliminatedVars);
  d_registry->unregisterStat(&d_statCallsToSolve);
  d_registry->unregisterStat(&d_statSolveTime);
}

void BVMinisatSatSolver::Statistics::init(BVMinisat::SimpSolver* minisat){
  if (!d_registerStats){
    return;
  }

  d_statStarts.setData(minisat->starts);
  d_statDecisions.setData(minisat->decisions);
  d_statRndDecisions.setData(minisat->rnd_decisions);
  d_statPropagations.setData(minisat->propagations);
  d_statConflicts.setData(minisat->conflicts);
  d_statClausesLiterals.setData(minisat->clauses_literals);
  d_statLearntsLiterals.setData(minisat->learnts_literals);
  d_statMaxLiterals.setData(minisat->max_literals);
  d_statTotLiterals.setData(minisat->tot_literals);
  d_statEliminatedVars.setData(minisat->eliminated_vars);
}

} /* namespace CVC4::prop */
} /* namespace CVC4 */
