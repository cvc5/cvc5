/*********************                                                        */
/*! \file minisat.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors:
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** Implementation of the minisat for cvc4.
 **/

#include "prop/minisat/minisat.h"
#include "prop/minisat/simp/SimpSolver.h"

using namespace CVC4;
using namespace CVC4::prop;

//// DPllMinisatSatSolver

MinisatSatSolver::MinisatSatSolver() :
  d_minisat(NULL),
  d_theoryProxy(NULL),
  d_context(NULL)
{}

MinisatSatSolver::~MinisatSatSolver() {
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

SatValue MinisatSatSolver::toSatLiteralValue(bool res) {
  if(res) return SAT_VALUE_TRUE;
  else return SAT_VALUE_FALSE;
}

SatValue MinisatSatSolver::toSatLiteralValue(Minisat::lbool res) {
  if(res == (Minisat::lbool((uint8_t)0))) return SAT_VALUE_TRUE;
  if(res == (Minisat::lbool((uint8_t)2))) return SAT_VALUE_UNKNOWN;
  Assert(res == (Minisat::lbool((uint8_t)1)));
  return SAT_VALUE_FALSE;
}


void MinisatSatSolver::toMinisatClause(SatClause& clause,
                                           Minisat::vec<Minisat::Lit>& minisat_clause) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    minisat_clause.push(toMinisatLit(clause[i]));
  }
  Assert(clause.size() == (unsigned)minisat_clause.size());
}

void MinisatSatSolver::toSatClause(Minisat::vec<Minisat::Lit>& clause,
                                       SatClause& sat_clause) {
  for (int i = 0; i < clause.size(); ++i) {
    sat_clause.push_back(toSatLiteral(clause[i]));
  }
  Assert((unsigned)clause.size() == sat_clause.size());
}


void MinisatSatSolver::initialize(context::Context* context, TheoryProxy* theoryProxy)
{

  d_context = context;

  // Create the solver
  d_minisat = new Minisat::SimpSolver(theoryProxy, d_context,
                                      Options::current()->incrementalSolving);
  // Setup the verbosity
  d_minisat->verbosity = (Options::current()->verbosity > 0) ? 1 : -1;

  // Setup the random decision parameters
  d_minisat->random_var_freq = Options::current()->satRandomFreq;
  d_minisat->random_seed = Options::current()->satRandomSeed;
  // Give access to all possible options in the sat solver
  d_minisat->var_decay = Options::current()->satVarDecay;
  d_minisat->clause_decay = Options::current()->satClauseDecay;
  d_minisat->restart_first = Options::current()->satRestartFirst;
  d_minisat->restart_inc = Options::current()->satRestartInc;

  d_statistics.init(d_minisat);
}

void MinisatSatSolver::addClause(SatClause& clause, bool removable) {
  Minisat::vec<Minisat::Lit> minisat_clause;
  toMinisatClause(clause, minisat_clause);
  d_minisat->addClause(minisat_clause, removable);
}

SatVariable MinisatSatSolver::newVar(bool theoryAtom) {
  return d_minisat->newVar(true, true, theoryAtom);
}


SatValue MinisatSatSolver::solve(unsigned long& resource) {
  Trace("limit") << "SatSolver::solve(): have limit of " << resource << " conflicts" << std::endl;
  if(resource == 0) {
    d_minisat->budgetOff();
  } else {
    d_minisat->setConfBudget(resource);
  }
  Minisat::vec<Minisat::Lit> empty;
  unsigned long conflictsBefore = d_minisat->conflicts;
  SatValue result = toSatLiteralValue(d_minisat->solveLimited(empty));
  d_minisat->clearInterrupt();
  resource = d_minisat->conflicts - conflictsBefore;
  Trace("limit") << "SatSolver::solve(): it took " << resource << " conflicts" << std::endl;
  return result;
}

SatValue MinisatSatSolver::solve() {
  d_minisat->budgetOff();
  return toSatLiteralValue(d_minisat->solve());
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

/** Incremental interface */

unsigned MinisatSatSolver::getAssertionLevel() const {
  return d_minisat->getAssertionLevel();
}

void MinisatSatSolver::push() {
  d_minisat->push();
}

void MinisatSatSolver::pop(){
  d_minisat->pop();
}

void MinisatSatSolver::unregisterVar(SatLiteral lit) {
  d_minisat->unregisterVar(toMinisatLit(lit));
}

void MinisatSatSolver::renewVar(SatLiteral lit, int level) {
  d_minisat->renewVar(toMinisatLit(lit), level);
}

/// Statistics for MinisatSatSolver

MinisatSatSolver::Statistics::Statistics() :
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
  StatisticsRegistry::registerStat(&d_statStarts);
  StatisticsRegistry::registerStat(&d_statDecisions);
  StatisticsRegistry::registerStat(&d_statRndDecisions);
  StatisticsRegistry::registerStat(&d_statPropagations);
  StatisticsRegistry::registerStat(&d_statConflicts);
  StatisticsRegistry::registerStat(&d_statClausesLiterals);
  StatisticsRegistry::registerStat(&d_statLearntsLiterals);
  StatisticsRegistry::registerStat(&d_statMaxLiterals);
  StatisticsRegistry::registerStat(&d_statTotLiterals);
}
MinisatSatSolver::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_statStarts);
  StatisticsRegistry::unregisterStat(&d_statDecisions);
  StatisticsRegistry::unregisterStat(&d_statRndDecisions);
  StatisticsRegistry::unregisterStat(&d_statPropagations);
  StatisticsRegistry::unregisterStat(&d_statConflicts);
  StatisticsRegistry::unregisterStat(&d_statClausesLiterals);
  StatisticsRegistry::unregisterStat(&d_statLearntsLiterals);
  StatisticsRegistry::unregisterStat(&d_statMaxLiterals);
  StatisticsRegistry::unregisterStat(&d_statTotLiterals);
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
