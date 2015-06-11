/*********************                                                        */
/*! \file riss.cpp
 ** \verbatim
 ** Original author: lianah
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
 ** Implementation of the riss sat solver for cvc4 (bitvectors).
 **/

#include "prop/riss.h"
#include "smt/options.h"

#ifdef CVC4_USE_RISS

#include "theory/bv/options.h"

using namespace CVC4;
using namespace prop;

RissSolver::RissSolver(const std::string& name)
  : d_config( CVC4::options::rissCommands() )
  , d_CP3Config(CVC4::options::rissCommands() )
  , d_solver(new Riss::Solver(&d_config))
  , d_statistics(name)
{
  // tell solver about preprocessor object
  d_solver->setPreprocessor(&d_CP3Config);
  
  // if (CVC4::options::produceModels()) {
  //   // FIXME: we don't want to freeze everything
  //   d_solver->use_elim  = false;
  // }
  d_true = newVar();
  d_false = newVar();
  d_solver->addClause(Riss::mkLit(d_true, false));
  d_solver->addClause(Riss::mkLit(d_false, true));
}


RissSolver::~RissSolver() throw(AssertionException) {
  delete d_solver;
}

void RissSolver::addClause(SatClause& clause, bool removable, uint64_t proof_id) {
  Debug("sat::riss") << "Add clause " << clause <<"\n";

  if (!d_solver->okay()) {
    Debug("sat::riss") << "Solver unsat: not adding clause.\n";
    return;
  }
  
  ++(d_statistics.d_clausesAdded);
  
  Riss::vec<Riss::Lit> internal_clause;
  toInternalClause(clause, internal_clause);
  d_solver->addClause(internal_clause); // check return status?
}

SatVariable  RissSolver::newVar(bool isTheoryAtom, bool preRegister, bool canErase){
  return d_solver->newVar();
}

SatVariable RissSolver::trueVar() {
  return d_true;
}

SatVariable RissSolver::falseVar() {
  return d_false;
}

void RissSolver::markUnremovable(SatLiteral lit) {
  d_solver->freezeVariable(lit.getSatVariable(), true);
  return;
}

void RissSolver::interrupt(){
  d_solver->interrupt();
}

SatValue RissSolver::solve(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveTime);
  ++d_statistics.d_statCallsToSolve;
  return toSatLiteralValue(d_solver->solve());
}

SatValue RissSolver::solve(long unsigned int& resource) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveTime);
  if(resource == 0) {
    d_solver->budgetOff();
  } else {
    d_solver->setConfBudget(resource);
  }
  return solve();
}

SatValue RissSolver::value(SatLiteral l){
  return toSatLiteralValue(d_solver->modelValue(toInternalLit(l)));
}

SatValue RissSolver::modelValue(SatLiteral l){
  return toSatLiteralValue(d_solver->modelValue(toInternalLit(l)));
}

unsigned RissSolver::getAssertionLevel() const {
  Unreachable("No interface to get assertion level in Riss");
  return -1; 
}

// converting from internal sat solver representation

SatVariable RissSolver::toSatVariable(Riss::Var var) {
  if (var == Riss::Var(-1)) {
    return undefSatVariable;
  }
  return SatVariable(var);
}

Riss::Lit RissSolver::toInternalLit(SatLiteral lit) {
  if (lit == undefSatLiteral) {
    return Riss::lit_Undef;
  }
  return Riss::mkLit(lit.getSatVariable(), lit.isNegated());
}

SatLiteral RissSolver::toSatLiteral(Riss::Lit lit) {
  if (lit == Riss::lit_Undef) {
    return undefSatLiteral;
  }

  return SatLiteral(SatVariable(Riss::var(lit)),
                    Riss::sign(lit));
}

SatValue RissSolver::toSatLiteralValue(Riss::lbool res) {
  if(res == Riss::lbool((uint8_t)0)/*Riss::l_True*/) return SAT_VALUE_TRUE;
  if(res == Riss::lbool((uint8_t)2)/*Riss::l_Undef*/) return SAT_VALUE_UNKNOWN;
  Assert(res == Riss::lbool((uint8_t)1)/*Riss::l_False*/);
  return SAT_VALUE_FALSE;
}

SatValue RissSolver::toSatLiteralValue(bool res) {
  if(res) return SAT_VALUE_TRUE;
  return SAT_VALUE_FALSE;
}


void RissSolver::toInternalClause(SatClause& clause,
                                           Riss::vec<Riss::Lit>& internal_clause) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    internal_clause.push(toInternalLit(clause[i]));
  }
  Assert(clause.size() == (unsigned)internal_clause.size());
}

void RissSolver::toSatClause(Riss::vec<Riss::Lit>& clause,
				SatClause& sat_clause) {
  for (int i = 0; i < clause.size(); ++i) {
    sat_clause.push_back(toSatLiteral(clause[i]));
  }
  Assert((unsigned)clause.size() == sat_clause.size());
}


// Satistics for RissSolver

RissSolver::Statistics::Statistics(const std::string& prefix) :
  d_statCallsToSolve("theory::bv::"+prefix+"::riss::calls_to_solve", 0),
  d_xorClausesAdded("theory::bv::"+prefix+"::riss::xor_clauses", 0),
  d_clausesAdded("theory::bv::"+prefix+"::riss::clauses", 0),
  d_solveTime("theory::bv::"+prefix+"::riss::solve_time"),
  d_registerStats(!prefix.empty())
{
  if (!d_registerStats)
    return;

  StatisticsRegistry::registerStat(&d_statCallsToSolve);
  StatisticsRegistry::registerStat(&d_xorClausesAdded);
  StatisticsRegistry::registerStat(&d_clausesAdded);
  StatisticsRegistry::registerStat(&d_solveTime);
}

RissSolver::Statistics::~Statistics() {
  if (!d_registerStats)
    return;

  StatisticsRegistry::unregisterStat(&d_statCallsToSolve);
  StatisticsRegistry::unregisterStat(&d_xorClausesAdded);
  StatisticsRegistry::unregisterStat(&d_clausesAdded);
  StatisticsRegistry::unregisterStat(&d_solveTime);
}

#endif // CVC4_USE_RISS
