/*********************                                                        */
/*! \file minisat.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors:
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2014  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** Implementation of the minisat interface for cvc4.
 **/

#include "prop/minisat/minisat.h"
#include "prop/minisat/simp/SimpSolver.h"
#include "prop/options.h"
#include "smt/options.h"
#include "decision/options.h"

using namespace CVC4;
using namespace CVC4::prop;

//// DPllMinisatSatSolver

MinisatSatSolver::MinisatSatSolver() :
  d_minisat(NULL),
  d_context(NULL)
{}

MinisatSatSolver::~MinisatSatSolver() throw()
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

void MinisatSatSolver::toSatClause(Minisat::vec<Minisat::Lit>& clause,
                                       SatClause& sat_clause) {
  for (int i = 0; i < clause.size(); ++i) {
    sat_clause.push_back(toSatLiteral(clause[i]));
  }
  Assert((unsigned)clause.size() == sat_clause.size());
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

  if( options::decisionMode() != decision::DECISION_STRATEGY_INTERNAL ) {
    Notice() << "minisat: Incremental solving is forced on (to avoid variable elimination)"
             << " unless using internal decision strategy." << std::endl;
  }

  // Create the solver
  d_minisat = new Minisat::SimpSolver(theoryProxy, d_context,
                                      options::incrementalSolving() ||
                                      options::decisionMode() != decision::DECISION_STRATEGY_INTERNAL );

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

void MinisatSatSolver::addClause(SatClause& clause, bool removable, uint64_t proof_id) {
  Minisat::vec<Minisat::Lit> minisat_clause;
  toMinisatClause(clause, minisat_clause);
  d_minisat->addClause(minisat_clause, removable, proof_id);
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

bool MinisatSatSolver::flipDecision() { 
  Debug("minisat") << "flipDecision()" << std::endl;
  return d_minisat->flipDecision();
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
