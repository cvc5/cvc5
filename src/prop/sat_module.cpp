/*********************                                                        */
/*! \file sat.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: dejan, taking, mdeters, lianah
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "prop/prop_engine.h"
#include "prop/sat_module.h"
#include "context/context.h"
#include "theory/theory_engine.h"
#include "expr/expr_stream.h"
#include "prop/sat.h"

using namespace std; 

namespace CVC4 {
namespace prop {

string SatLiteral::toString() {
  ostringstream os;
  os << (isNegated()? "~" : "") << getSatVariable() << " ";
  return os.str(); 
}

MinisatSatSolver::MinisatSatSolver() :
  d_minisat(new BVMinisat::SimpSolver())
{
  d_statistics.init(d_minisat); 
}

void MinisatSatSolver::addClause(SatClause& clause, bool removable) {
  Debug("sat::minisat") << "Add clause " << clause <<"\n"; 
  BVMinisat::vec<BVMinisat::Lit> minisat_clause;
  toMinisatClause(clause, minisat_clause); 
  d_minisat->addClause(minisat_clause);
}

SatVariable MinisatSatSolver::newVar(bool freeze){
  return d_minisat->newVar(true, true, freeze);
}

void MinisatSatSolver::markUnremovable(SatLiteral lit){
  d_minisat->setFrozen(BVMinisat::var(toMinisatLit(lit)), true);
}
 
void MinisatSatSolver::interrupt(){
  d_minisat->interrupt(); 
}

SatLiteralValue MinisatSatSolver::solve(){
  return toSatLiteralValue(d_minisat->solve()); 
}

SatLiteralValue MinisatSatSolver::solve(long unsigned int& resource){
  Trace("limit") << "MinisatSatSolver::solve(): have limit of " << resource << " conflicts" << std::endl;
  if(resource == 0) {
    d_minisat->budgetOff();
  } else {
    d_minisat->setConfBudget(resource);
  }
  BVMinisat::vec<BVMinisat::Lit> empty;
  unsigned long conflictsBefore = d_minisat->conflicts;
  SatLiteralValue result = toSatLiteralValue(d_minisat->solveLimited(empty));
  d_minisat->clearInterrupt();
  resource = d_minisat->conflicts - conflictsBefore;
  Trace("limit") << "<MinisatSatSolver::solve(): it took " << resource << " conflicts" << std::endl;
  return result;
}

SatLiteralValue MinisatSatSolver::solve(const context::CDList<SatLiteral> & assumptions){
  Debug("sat::minisat") << "Solve with assumptions ";
  context::CDList<SatLiteral>::const_iterator it = assumptions.begin();
  BVMinisat::vec<BVMinisat::Lit> assump; 
  for(; it!= assumptions.end(); ++it) {
    SatLiteral lit = *it;
    Debug("sat::minisat") << lit <<" "; 
    assump.push(toMinisatLit(lit)); 
  }
  Debug("sat::minisat") <<"\n";
  
 SatLiteralValue result = toSatLiteralValue(d_minisat->solve(assump)); 
 return result;
}


void MinisatSatSolver::getUnsatCore(SatClause& unsatCore) {
  // TODO add assertion to check the call was after an unsat call
  for (int i = 0; i < d_minisat->conflict.size(); ++i) {
    unsatCore.push_back(toSatLiteral(d_minisat->conflict[i])); 
  }
}

SatLiteralValue MinisatSatSolver::value(SatLiteral l){
    Unimplemented();
    return SatValUnknown; 
}

SatLiteralValue MinisatSatSolver::modelValue(SatLiteral l){
    Unimplemented();
    return SatValUnknown; 
}

void MinisatSatSolver::unregisterVar(SatLiteral lit) {
  // this should only be called when user context is implemented
  // in the BVSatSolver 
  Unreachable();
}

void MinisatSatSolver::renewVar(SatLiteral lit, int level) {
  // this should only be called when user context is implemented
  // in the BVSatSolver 

  Unreachable(); 
}

int MinisatSatSolver::getAssertionLevel() const {
  // we have no user context implemented so far
  return 0;
}

// converting from internal Minisat representation

SatVariable MinisatSatSolver::toSatVariable(BVMinisat::Var var) {
  if (var == var_Undef) {
    return undefSatVariable; 
  }
  return SatVariable(var);
}

BVMinisat::Lit MinisatSatSolver::toMinisatLit(SatLiteral lit) {
  if (lit == undefSatLiteral) {
    return BVMinisat::lit_Undef;
  }
  return BVMinisat::mkLit(lit.getSatVariable(), lit.isNegated()); 
}

SatLiteral MinisatSatSolver::toSatLiteral(BVMinisat::Lit lit) {
  if (lit == BVMinisat::lit_Undef) {
    return undefSatLiteral; 
  }
  
  return SatLiteral(SatVariable(BVMinisat::var(lit)),
                    BVMinisat::sign(lit)); 
}

SatLiteralValue MinisatSatSolver::toSatLiteralValue(bool res) {
  if(res) return SatValTrue;
  else return SatValFalse; 
}

SatLiteralValue MinisatSatSolver::toSatLiteralValue(BVMinisat::lbool res) {
  if(res == (BVMinisat::lbool((uint8_t)0))) return SatValTrue;
  if(res == (BVMinisat::lbool((uint8_t)2))) return SatValUnknown;
  Assert(res == (BVMinisat::lbool((uint8_t)1)));
  return SatValFalse; 
}

void MinisatSatSolver::toMinisatClause(SatClause& clause,
                                           BVMinisat::vec<BVMinisat::Lit>& minisat_clause) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    minisat_clause.push(toMinisatLit(clause[i])); 
  }
  Assert(clause.size() == minisat_clause.size()); 
}

void MinisatSatSolver::toSatClause(BVMinisat::vec<BVMinisat::Lit>& clause,
                                       SatClause& sat_clause) {
  for (int i = 0; i < clause.size(); ++i) {
    sat_clause.push_back(toSatLiteral(clause[i])); 
  }
  Assert(clause.size() == sat_clause.size()); 
}


//// DPllMinisatSatSolver

DPLLMinisatSatSolver::DPLLMinisatSatSolver() :
  d_minisat(NULL), 
  d_theoryProxy(NULL),
  d_context(NULL)
{}

DPLLMinisatSatSolver::~DPLLMinisatSatSolver() {
  delete d_minisat; 
}

SatVariable DPLLMinisatSatSolver::toSatVariable(Minisat::Var var) {
  if (var == var_Undef) {
    return undefSatVariable; 
  }
  return SatVariable(var);
}

Minisat::Lit DPLLMinisatSatSolver::toMinisatLit(SatLiteral lit) {
  if (lit == undefSatLiteral) {
    return Minisat::lit_Undef;
  }
  return Minisat::mkLit(lit.getSatVariable(), lit.isNegated()); 
}

SatLiteral DPLLMinisatSatSolver::toSatLiteral(Minisat::Lit lit) {
  if (lit == Minisat::lit_Undef) {
    return undefSatLiteral; 
  }
  
  return SatLiteral(SatVariable(Minisat::var(lit)),
                    Minisat::sign(lit)); 
}

SatLiteralValue DPLLMinisatSatSolver::toSatLiteralValue(bool res) {
  if(res) return SatValTrue;
  else return SatValFalse; 
}

SatLiteralValue DPLLMinisatSatSolver::toSatLiteralValue(Minisat::lbool res) {
  if(res == (Minisat::lbool((uint8_t)0))) return SatValTrue;
  if(res == (Minisat::lbool((uint8_t)2))) return SatValUnknown;
  Assert(res == (Minisat::lbool((uint8_t)1)));
  return SatValFalse; 
}


void DPLLMinisatSatSolver::toMinisatClause(SatClause& clause,
                                           Minisat::vec<Minisat::Lit>& minisat_clause) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    minisat_clause.push(toMinisatLit(clause[i])); 
  }
  Assert(clause.size() == minisat_clause.size()); 
}

void DPLLMinisatSatSolver::toSatClause(Minisat::vec<Minisat::Lit>& clause,
                                       SatClause& sat_clause) {
  for (int i = 0; i < clause.size(); ++i) {
    sat_clause.push_back(toSatLiteral(clause[i])); 
  }
  Assert(clause.size() == sat_clause.size()); 
}


void DPLLMinisatSatSolver::initialize(context::Context* context, TheoryProxy* theoryProxy)
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

void DPLLMinisatSatSolver::addClause(SatClause& clause, bool removable) {
  Minisat::vec<Minisat::Lit> minisat_clause;
  toMinisatClause(clause, minisat_clause); 
  d_minisat->addClause(minisat_clause, removable);
}

SatVariable DPLLMinisatSatSolver::newVar(bool theoryAtom) {
  return d_minisat->newVar(true, true, theoryAtom);
}

  
SatLiteralValue DPLLMinisatSatSolver::solve(unsigned long& resource) {
  Trace("limit") << "SatSolver::solve(): have limit of " << resource << " conflicts" << std::endl;
  if(resource == 0) {
    d_minisat->budgetOff();
  } else {
    d_minisat->setConfBudget(resource);
  }
  Minisat::vec<Minisat::Lit> empty;
  unsigned long conflictsBefore = d_minisat->conflicts;
  SatLiteralValue result = toSatLiteralValue(d_minisat->solveLimited(empty));
  d_minisat->clearInterrupt();
  resource = d_minisat->conflicts - conflictsBefore;
  Trace("limit") << "SatSolver::solve(): it took " << resource << " conflicts" << std::endl;
  return result;
}

SatLiteralValue DPLLMinisatSatSolver::solve() {
  d_minisat->budgetOff();
  return toSatLiteralValue(d_minisat->solve()); 
}


void DPLLMinisatSatSolver::interrupt() {
  d_minisat->interrupt();
}

SatLiteralValue DPLLMinisatSatSolver::value(SatLiteral l) {
  return toSatLiteralValue(d_minisat->value(toMinisatLit(l)));
}

SatLiteralValue DPLLMinisatSatSolver::modelValue(SatLiteral l){
  return toSatLiteralValue(d_minisat->modelValue(toMinisatLit(l)));
}


/** Incremental interface */ 
  
int DPLLMinisatSatSolver::getAssertionLevel() const {
  return d_minisat->getAssertionLevel(); 
}
  
void DPLLMinisatSatSolver::push() {
  d_minisat->push();
}

void DPLLMinisatSatSolver::pop(){
  d_minisat->pop();
}

void DPLLMinisatSatSolver::unregisterVar(SatLiteral lit) {
  d_minisat->unregisterVar(toMinisatLit(lit));
}

void DPLLMinisatSatSolver::renewVar(SatLiteral lit, int level) {
  d_minisat->renewVar(toMinisatLit(lit), level);
}

MinisatSatSolver* SatSolverFactory::createMinisat() {
  return new MinisatSatSolver(); 
}

DPLLMinisatSatSolver* SatSolverFactory::createDPLLMinisat(){
  return new DPLLMinisatSatSolver(); 
} 


}/* CVC4::prop namespace */
}/* CVC4 namespace */
