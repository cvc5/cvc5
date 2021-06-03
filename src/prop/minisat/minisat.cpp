/******************************************************************************
 * Top contributors (to current version):
 *   Dejan Jovanovic, Liana Hadarean, Morgan Deters
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
 * Implementation of the minisat interface for cvc5.
 */

#include "prop/minisat/minisat.h"

#include "options/base_options.h"
#include "options/decision_options.h"
#include "options/prop_options.h"
#include "options/smt_options.h"
#include "proof/clause_id.h"
#include "prop/minisat/simp/SimpSolver.h"
#include "util/statistics_stats.h"

namespace cvc5 {
namespace prop {

//// DPllMinisatSatSolver

MinisatSatSolver::MinisatSatSolver(StatisticsRegistry& registry)
    : d_minisat(NULL), d_context(NULL), d_assumptions(), d_statistics(registry)
{}

MinisatSatSolver::~MinisatSatSolver()
{
  d_statistics.deinit();
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

void MinisatSatSolver::initialize(context::Context* context,
                                  TheoryProxy* theoryProxy,
                                  context::UserContext* userContext,
                                  ProofNodeManager* pnm)
{
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
      userContext,
      pnm,
      options::incrementalSolving()
          || options::decisionMode() != options::DecisionMode::INTERNAL);

  d_statistics.init(d_minisat);
}

// Like initialize() above, but called just before each search when in
// incremental mode
void MinisatSatSolver::setupOptions() {
  // Copy options from cvc5 options structure into minisat, as appropriate

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
  // FIXME: to be deleted when we kill old proof code for unsat cores
  Assert(!options::unsatCores() || options::produceProofs()
         || clause_id != ClauseIdError);
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
  SatValue result = toSatLiteralValue(d_minisat->solve());
  d_minisat->clearInterrupt();
  return result;
}

SatValue MinisatSatSolver::solve(const std::vector<SatLiteral>& assumptions)
{
  setupOptions();
  d_minisat->budgetOff();

  d_assumptions.clear();
  Minisat::vec<Minisat::Lit> assumps;

  for (const SatLiteral& lit : assumptions)
  {
    Minisat::Lit mlit = toMinisatLit(lit);
    assumps.push(mlit);
    d_assumptions.emplace(lit);
  }

  SatValue result = toSatLiteralValue(d_minisat->solve(assumps));
  d_minisat->clearInterrupt();
  return result;
}

void MinisatSatSolver::getUnsatAssumptions(
    std::vector<SatLiteral>& unsat_assumptions)
{
  for (size_t i = 0, size = d_minisat->d_conflict.size(); i < size; ++i)
  {
    Minisat::Lit mlit = d_minisat->d_conflict[i];
    SatLiteral lit = ~toSatLiteral(mlit);
    if (d_assumptions.find(lit) != d_assumptions.end())
    {
      unsat_assumptions.push_back(lit);
    }
  }
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

int32_t MinisatSatSolver::getDecisionLevel(SatVariable v) const
{
  return d_minisat->level(v);
}

int32_t MinisatSatSolver::getIntroLevel(SatVariable v) const
{
  return d_minisat->intro_level(v);
}

SatProofManager* MinisatSatSolver::getProofManager()
{
  return d_minisat->getProofManager();
}

std::shared_ptr<ProofNode> MinisatSatSolver::getProof()
{
  return d_minisat->getProof();
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

MinisatSatSolver::Statistics::Statistics(StatisticsRegistry& registry)
    : d_statStarts(registry.registerReference<int64_t>("sat::starts")),
      d_statDecisions(registry.registerReference<int64_t>("sat::decisions")),
      d_statRndDecisions(
          registry.registerReference<int64_t>("sat::rnd_decisions")),
      d_statPropagations(
          registry.registerReference<int64_t>("sat::propagations")),
      d_statConflicts(registry.registerReference<int64_t>("sat::conflicts")),
      d_statClausesLiterals(
          registry.registerReference<int64_t>("sat::clauses_literals")),
      d_statLearntsLiterals(
          registry.registerReference<int64_t>("sat::learnts_literals")),
      d_statMaxLiterals(
          registry.registerReference<int64_t>("sat::max_literals")),
      d_statTotLiterals(
          registry.registerReference<int64_t>("sat::tot_literals"))
{
}

void MinisatSatSolver::Statistics::init(Minisat::SimpSolver* minisat){
  d_statStarts.set(minisat->starts);
  d_statDecisions.set(minisat->decisions);
  d_statRndDecisions.set(minisat->rnd_decisions);
  d_statPropagations.set(minisat->propagations);
  d_statConflicts.set(minisat->conflicts);
  d_statClausesLiterals.set(minisat->clauses_literals);
  d_statLearntsLiterals.set(minisat->learnts_literals);
  d_statMaxLiterals.set(minisat->max_literals);
  d_statTotLiterals.set(minisat->tot_literals);
}
void MinisatSatSolver::Statistics::deinit()
{
  d_statStarts.reset();
  d_statDecisions.reset();
  d_statRndDecisions.reset();
  d_statPropagations.reset();
  d_statConflicts.reset();
  d_statClausesLiterals.reset();
  d_statLearntsLiterals.reset();
  d_statMaxLiterals.reset();
  d_statTotLiterals.reset();
}

}  // namespace prop
}  // namespace cvc5

namespace cvc5 {
template <>
prop::SatLiteral toSatLiteral<cvc5::Minisat::Solver>(Minisat::Solver::TLit lit)
{
  return prop::MinisatSatSolver::toSatLiteral(lit);
}

template <>
void toSatClause<cvc5::Minisat::Solver>(
    const cvc5::Minisat::Solver::TClause& minisat_cl, prop::SatClause& sat_cl)
{
  prop::MinisatSatSolver::toSatClause(minisat_cl, sat_cl);
}

}  // namespace cvc5
