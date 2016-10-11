/*********************                                                        */
/*! \file cryptominisat.cpp
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
 ** Implementation of the cryptominisat for cvc4 (bitvectors).
 **/

#include "prop/cryptominisat.h"

#include "proof/clause_id.h"
#include "proof/sat_proof.h"

using namespace CVC4;
using namespace prop;

#ifdef CVC4_USE_CRYPTOMINISAT

CryptoMinisatSolver::CryptoMinisatSolver(StatisticsRegistry* registry,
                                         const std::string& name)
: d_solver(new CMSat::SATSolver())
, d_numVariables(0)
, d_okay(true)
, d_statistics(registry, name)
{
  d_true = newVar();
  d_false = newVar();

  std::vector<CMSat::Lit> clause(1);
  clause[0] = CMSat::Lit(d_true, false);
  d_solver->add_clause(clause);
  
  clause[0] = CMSat::Lit(d_false, true);
  d_solver->add_clause(clause);
}


CryptoMinisatSolver::~CryptoMinisatSolver() {
  delete d_solver;
}

ClauseId CryptoMinisatSolver::addXorClause(SatClause& clause,
				       bool rhs,
				       bool removable) {
  Debug("sat::cryptominisat") << "Add xor clause " << clause <<" = " << rhs << "\n";

  if (!d_okay) {
    Debug("sat::cryptominisat") << "Solver unsat: not adding clause.\n";
    return ClauseIdError;
  }

  ++(d_statistics.d_xorClausesAdded);
  
  // ensure all sat literals have positive polarity by pushing
  // the negation on the result
  std::vector<CMSat::Var> xor_clause;
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
  bool res = d_solver->add_clause(internal_clause);
  d_okay &= res;
  return ClauseIdError;
}

bool CryptoMinisatSolver::ok() const {
  return d_okay; 
}


SatVariable  CryptoMinisatSolver::newVar(bool isTheoryAtom, bool preRegister, bool canErase){
  d_solver->new_var();
  ++d_numVariables;
  Assert (d_numVariables == d_solver->nVars());
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
  Unreachable("Not sure how to set different limits for calls to solve in Cryptominisat"); 
  return solve();
}

SatValue CryptoMinisatSolver::value(SatLiteral l){
  const std::vector<CMSat::lbool> model = d_solver->get_model();
  CMSat::Var var = l.getSatVariable();
  Assert (var < model.size());
  CMSat::lbool value = model[var];
  return toSatLiteralValue(value);
}

SatValue CryptoMinisatSolver::modelValue(SatLiteral l){
  return value(l); 
}

unsigned CryptoMinisatSolver::getAssertionLevel() const {
  Unreachable("No interface to get assertion level in Cryptominisat");
  return -1; 
}

// converting from internal sat solver representation

SatVariable CryptoMinisatSolver::toSatVariable(CMSat::Var var) {
  if (var == CMSat::var_Undef) {
    return undefSatVariable;
  }
  return SatVariable(var);
}

CMSat::Lit CryptoMinisatSolver::toInternalLit(SatLiteral lit) {
  if (lit == undefSatLiteral) {
    return CMSat::lit_Undef;
  }
  return CMSat::Lit(lit.getSatVariable(), lit.isNegated());
}

SatLiteral CryptoMinisatSolver::toSatLiteral(CMSat::Lit lit) {
  Assert (lit != CMSat::lit_Error);
  if (lit == CMSat::lit_Undef) {
    return undefSatLiteral;
  }

  return SatLiteral(SatVariable(lit.var()),
                    lit.sign());
}

SatValue CryptoMinisatSolver::toSatLiteralValue(CMSat::lbool res) {
  if(res == CMSat::l_True) return SAT_VALUE_TRUE;
  if(res == CMSat::l_Undef) return SAT_VALUE_UNKNOWN;
  Assert(res == CMSat::l_False);
  return SAT_VALUE_FALSE;
}

void CryptoMinisatSolver::toInternalClause(SatClause& clause,
                                           std::vector<CMSat::Lit>& internal_clause) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    internal_clause.push_back(toInternalLit(clause[i]));
  }
  Assert(clause.size() == internal_clause.size());
}

void CryptoMinisatSolver::toSatClause(std::vector<CMSat::Lit>& clause,
                                       SatClause& sat_clause) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    sat_clause.push_back(toSatLiteral(clause[i]));
  }
  Assert(clause.size() == sat_clause.size());
}


// Satistics for CryptoMinisatSolver

CryptoMinisatSolver::Statistics::Statistics(StatisticsRegistry* registry,
                                            const std::string& prefix) :
  d_registry(registry),
  d_statCallsToSolve("theory::bv::"+prefix+"::cryptominisat::calls_to_solve", 0),
  d_xorClausesAdded("theory::bv::"+prefix+"::cryptominisat::xor_clauses", 0),
  d_clausesAdded("theory::bv::"+prefix+"::cryptominisat::clauses", 0),
  d_solveTime("theory::bv::"+prefix+"::cryptominisat::solve_time"),
  d_registerStats(!prefix.empty())
{
  if (!d_registerStats)
    return;

  d_registry->registerStat(&d_statCallsToSolve);
  d_registry->registerStat(&d_xorClausesAdded);
  d_registry->registerStat(&d_clausesAdded);
  d_registry->registerStat(&d_solveTime);
}

CryptoMinisatSolver::Statistics::~Statistics() {
  if (!d_registerStats)
    return;
  d_registry->unregisterStat(&d_statCallsToSolve);
  d_registry->unregisterStat(&d_xorClausesAdded);
  d_registry->unregisterStat(&d_clausesAdded);
  d_registry->unregisterStat(&d_solveTime);
}
#endif
