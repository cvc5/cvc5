/*********************                                                        */
/*! \file minisat.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Dejan Jovanovic, Tim King
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

#include "prop/minisat/minisat.h"

#include "options/base_options.h"
#include "options/decision_options.h"
#include "options/prop_options.h"
#include "options/smt_options.h"
#include "prop/minisat/simp/SimpSolver.h"
#include "proof/clause_id.h"
#include "proof/sat_proof.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace prop {

//// DPllMinisatSatSolver

MinisatSatSolver::MinisatSatSolver(StatisticsRegistry* registry) :
  d_minisat(NULL),
  d_context(NULL),
  d_statistics(registry)
{}

MinisatSatSolver::~MinisatSatSolver()
{
  delete d_minisat;
}

SatVariable MinisatSatSolver::toSatVariable(Minisat::Var var) {
  if (var == var_Undef) {
    return undefSatVariable;
  }
  return SatVariable(var);
}

Minisat::Lit MinisatSatSolver::toMinisatLit(SatLiteral lit) {
  if (lit == undefSatLiteral) {
    return Minisat::lit_Undef;
  }
  return Minisat::mkLit(lit.getSatVariable(), lit.isNegated());
}

SatLiteral MinisatSatSolver::toSatLiteral(Minisat::Lit lit) {
  if (lit == Minisat::lit_Undef) {
    return undefSatLiteral;
  }

  return SatLiteral(SatVariable(Minisat::var(lit)),
                    Minisat::sign(lit));
}

SatValue MinisatSatSolver::toSatLiteralValue(Minisat::lbool res) {
  if(res == (Minisat::lbool((uint8_t)0))) return SAT_VALUE_TRUE;
  if(res == (Minisat::lbool((uint8_t)2))) return SAT_VALUE_UNKNOWN;
  Assert(res == (Minisat::lbool((uint8_t)1)));
  return SAT_VALUE_FALSE;
}

Minisat::lbool MinisatSatSolver::toMinisatlbool(SatValue val)
{
  if(val == SAT_VALUE_TRUE) return Minisat::lbool((uint8_t)0);
  if(val == SAT_VALUE_UNKNOWN) return Minisat::lbool((uint8_t)2);
  Assert(val == SAT_VALUE_FALSE);
  return Minisat::lbool((uint8_t)1);
}

/*bool MinisatSatSolver::tobool(SatValue val)
{
  if(val == SAT_VALUE_TRUE) return true;
  Assert(val == SAT_VALUE_FALSE);
  return false;
  }*/

void MinisatSatSolver::toMinisatClause(SatClause& clause,
                                           Minisat::vec<Minisat::Lit>& minisat_clause) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    minisat_clause.push(toMinisatLit(clause[i]));
  }
  Assert(clause.size() == (unsigned)minisat_clause.size());
}

void MinisatSatSolver::toSatClause(const Minisat::Clause& clause,
                                       SatClause& sat_clause) {
  for (int i = 0; i < clause.size(); ++i) {
    sat_clause.push_back(toSatLiteral(clause[i]));
  }
  Assert((unsigned)clause.size() == sat_clause.size());
}

void MinisatSatSolver::initialize(context::Context* context, TheoryProxy* theoryProxy) {

  d_context = context;

  if (options::decisionMode() != options::DecisionMode::INTERNAL)
  {
    Notice() << "minisat: Incremental solving is forced on (to avoid variable elimination)"
             << " unless using internal decision strategy." << std::endl;
  }

  // Create the solver
  d_minisat = new Minisat::SimpSolver(
      theoryProxy,
      d_context,
      options::incrementalSolving()
          || options::decisionMode() != options::DecisionMode::INTERNAL);

  d_statistics.init(d_minisat);
}

// Like initialize() above, but called just before each search when in
// incremental mode
void MinisatSatSolver::setupOptions() {
  // Copy options from CVC4 options structure into minisat, as appropriate

  // Set up the verbosity
  d_minisat->verbosity = (options::verbosity() > 0) ? 1 : -1;

  // Set up the random decision parameters
  d_minisat->random_var_freq = options::satRandomFreq();
  // If 0, we use whatever we like (here, the Minisat default seed)
  if(options::satRandomSeed() != 0) {
    d_minisat->random_seed = double(options::satRandomSeed());
  }

  // Give access to all possible options in the sat solver
  d_minisat->var_decay = options::satVarDecay();
  d_minisat->clause_decay = options::satClauseDecay();
  d_minisat->restart_first = options::satRestartFirst();
  d_minisat->restart_inc = options::satRestartInc();
}

ClauseId MinisatSatSolver::addClause(SatClause& clause, bool removable) {
  Minisat::vec<Minisat::Lit> minisat_clause;
  toMinisatClause(clause, minisat_clause);
  ClauseId clause_id = ClauseIdError;
  // FIXME: This relies on the invariant that when ok() is false
  // the SAT solver does not add the clause (which is what Minisat currently does)
  if (!ok()) {
    return ClauseIdUndef;
  }
  d_minisat->addClause(minisat_clause, removable, clause_id);
  Assert(!CVC4::options::unsatCores() || clause_id != ClauseIdError);
  return clause_id;
}

SatVariable MinisatSatSolver::newVar(bool isTheoryAtom, bool preRegister, bool canErase) {
  return d_minisat->newVar(true, true, isTheoryAtom, preRegister, canErase);
}

SatValue MinisatSatSolver::solve(unsigned long& resource) {
  Trace("limit") << "SatSolver::solve(): have limit of " << resource << " conflicts" << std::endl;
  setupOptions();
  if(resource == 0) {
    d_minisat->budgetOff();
  } else {
    d_minisat->setConfBudget(resource);
  }
  Minisat::vec<Minisat::Lit> empty;
  unsigned long conflictsBefore = d_minisat->conflicts + d_minisat->resources_consumed;
  SatValue result = toSatLiteralValue(d_minisat->solveLimited(empty));
  d_minisat->clearInterrupt();
  resource = d_minisat->conflicts + d_minisat->resources_consumed - conflictsBefore;
  Trace("limit") << "SatSolver::solve(): it took " << resource << " conflicts" << std::endl;
  return result;
}

SatValue MinisatSatSolver::solve() {
  setupOptions();
  d_minisat->budgetOff();
  return toSatLiteralValue(d_minisat->solve());
}

bool MinisatSatSolver::ok() const {
  return d_minisat->okay();
}

void MinisatSatSolver::interrupt() {
  d_minisat->interrupt();
}

SatValue MinisatSatSolver::value(SatLiteral l) {
  return toSatLiteralValue(d_minisat->value(toMinisatLit(l)));
}

SatValue MinisatSatSolver::modelValue(SatLiteral l){
  return toSatLiteralValue(d_minisat->modelValue(toMinisatLit(l)));
}

bool MinisatSatSolver::properExplanation(SatLiteral lit, SatLiteral expl) const {
  return true;
}

void MinisatSatSolver::requirePhase(SatLiteral lit) {
  Assert(!d_minisat->rnd_pol);
  Debug("minisat") << "requirePhase(" << lit << ")" << " " <<  lit.getSatVariable() << " " << lit.isNegated() << std::endl;
  SatVariable v = lit.getSatVariable();
  d_minisat->freezePolarity(v, lit.isNegated());
}

bool MinisatSatSolver::isDecision(SatVariable decn) const {
  return d_minisat->isDecision( decn );
}

/** Incremental interface */

unsigned MinisatSatSolver::getAssertionLevel() const {
  return d_minisat->getAssertionLevel();
}

void MinisatSatSolver::push() {
  d_minisat->push();
}

void MinisatSatSolver::pop() {
  d_minisat->pop();
}

void MinisatSatSolver::resetTrail() { d_minisat->resetTrail(); }

/// Statistics for MinisatSatSolver

MinisatSatSolver::Statistics::Statistics(StatisticsRegistry* registry) :
    d_registry(registry),
    d_statStarts("sat::starts"),
    d_statDecisions("sat::decisions"),
    d_statRndDecisions("sat::rnd_decisions"),
    d_statPropagations("sat::propagations"),
    d_statConflicts("sat::conflicts"),
    d_statClausesLiterals("sat::clauses_literals"),
    d_statLearntsLiterals("sat::learnts_literals"),
    d_statMaxLiterals("sat::max_literals"),
    d_statTotLiterals("sat::tot_literals")
{
  d_registry->registerStat(&d_statStarts);
  d_registry->registerStat(&d_statDecisions);
  d_registry->registerStat(&d_statRndDecisions);
  d_registry->registerStat(&d_statPropagations);
  d_registry->registerStat(&d_statConflicts);
  d_registry->registerStat(&d_statClausesLiterals);
  d_registry->registerStat(&d_statLearntsLiterals);
  d_registry->registerStat(&d_statMaxLiterals);
  d_registry->registerStat(&d_statTotLiterals);
}

MinisatSatSolver::Statistics::~Statistics() {
  d_registry->unregisterStat(&d_statStarts);
  d_registry->unregisterStat(&d_statDecisions);
  d_registry->unregisterStat(&d_statRndDecisions);
  d_registry->unregisterStat(&d_statPropagations);
  d_registry->unregisterStat(&d_statConflicts);
  d_registry->unregisterStat(&d_statClausesLiterals);
  d_registry->unregisterStat(&d_statLearntsLiterals);
  d_registry->unregisterStat(&d_statMaxLiterals);
  d_registry->unregisterStat(&d_statTotLiterals);
}

void MinisatSatSolver::Statistics::init(Minisat::SimpSolver* d_minisat){
  d_statStarts.setData(d_minisat->starts);
  d_statDecisions.setData(d_minisat->decisions);
  d_statRndDecisions.setData(d_minisat->rnd_decisions);
  d_statPropagations.setData(d_minisat->propagations);
  d_statConflicts.setData(d_minisat->conflicts);
  d_statClausesLiterals.setData(d_minisat->clauses_literals);
  d_statLearntsLiterals.setData(d_minisat->learnts_literals);
  d_statMaxLiterals.setData(d_minisat->max_literals);
  d_statTotLiterals.setData(d_minisat->tot_literals);
}

} /* namespace CVC4::prop */
} /* namespace CVC4 */


namespace CVC4 {
template<>
prop::SatLiteral toSatLiteral< CVC4::Minisat::Solver>(Minisat::Solver::TLit lit) {
  return prop::MinisatSatSolver::toSatLiteral(lit);
}

template<>
void toSatClause< CVC4::Minisat::Solver> (const CVC4::Minisat::Solver::TClause& minisat_cl,
                                      prop::SatClause& sat_cl) {
  prop::MinisatSatSolver::toSatClause(minisat_cl, sat_cl);
}

} /* namespace CVC4 */
