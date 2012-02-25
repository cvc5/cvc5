/*********************                                                        */
/*! \file sat_module.h
 ** \verbatim
 ** Original author: lianah
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
 ** SAT Solver.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROP__SAT_MODULE_H
#define __CVC4__PROP__SAT_MODULE_H

#include <stdint.h> 
#include "util/options.h"
#include "util/stats.h"


// DPLLT Minisat
#include "prop/minisat/core/Solver.h"
#include "prop/minisat/core/SolverTypes.h"
#include "prop/minisat/simp/SimpSolver.h"

// BV Minisat
#include "prop/bvminisat/core/Solver.h"
#include "prop/bvminisat/core/SolverTypes.h"
#include "prop/bvminisat/simp/SimpSolver.h"


namespace CVC4 {
namespace prop {

class TheoryProxy; 

enum SatLiteralValue {
  SatValUnknown,
  SatValTrue, 
  SatValFalse 
};


typedef uint64_t SatVariable; 
// special constant
const SatVariable undefSatVariable = SatVariable(-1); 

class SatLiteral {
  uint64_t d_value;
public:
  SatLiteral() :
    d_value(undefSatVariable)
  {}
  
  SatLiteral(SatVariable var, bool negated = false) { d_value = var + var + (int)negated; }
  SatLiteral operator~() {
    return SatLiteral(getSatVariable(), !isNegated()); 
  }
  bool operator==(const SatLiteral& other) const {
    return d_value == other.d_value; 
  }
  bool operator!=(const SatLiteral& other) const {
    return !(*this == other); 
  }
  std::string toString();
  bool isNegated() const { return d_value & 1; }
  size_t toHash() const {return (size_t)d_value; }
  bool isNull() const { return d_value == (uint64_t)-1; }
  SatVariable getSatVariable() const {return d_value >> 1; }
};

// special constant 
const SatLiteral undefSatLiteral = SatLiteral(undefSatVariable);  


struct SatLiteralHashFunction {
  inline size_t operator() (const SatLiteral& literal) const {
    return literal.toHash();
  }
};

typedef std::vector<SatLiteral> SatClause;



class SatSolverInterface {
public:  
  /** Virtual destructor to make g++ happy */
  virtual ~SatSolverInterface() { }
  
  /** Assert a clause in the solver. */
  virtual void addClause(SatClause& clause, bool removable) = 0;

  /** Create a new boolean variable in the solver. */
  virtual SatVariable newVar(bool theoryAtom = false) = 0;

 
  /** Check the satisfiability of the added clauses */
  virtual SatLiteralValue solve() = 0;

  /** Check the satisfiability of the added clauses */
  virtual SatLiteralValue solve(long unsigned int&) = 0;
  
  /** Interrupt the solver */
  virtual void interrupt() = 0;

  /** Call value() during the search.*/
  virtual SatLiteralValue value(SatLiteral l) = 0;

  /** Call modelValue() when the search is done.*/
  virtual SatLiteralValue modelValue(SatLiteral l) = 0;

  virtual void unregisterVar(SatLiteral lit) = 0;
  
  virtual void renewVar(SatLiteral lit, int level = -1) = 0;

  virtual int getAssertionLevel() const = 0;

};


class BVSatSolverInterface: public SatSolverInterface {
public:
  virtual SatLiteralValue solve(const context::CDList<SatLiteral> & assumptions) = 0;

  virtual void markUnremovable(SatLiteral lit) = 0;

  virtual void getUnsatCore(SatClause& unsatCore) = 0; 
}; 


class DPLLSatSolverInterface: public SatSolverInterface {
public:
  virtual void initialize(context::Context* context, prop::TheoryProxy* theoryProxy) = 0; 
  
  virtual void push() = 0;

  virtual void pop() = 0;

}; 

// toodo add ifdef


class MinisatSatSolver: public BVSatSolverInterface {
  BVMinisat::SimpSolver* d_minisat; 

  MinisatSatSolver();
public:
  ~MinisatSatSolver() {delete d_minisat;}
  void addClause(SatClause& clause, bool removable);

  SatVariable newVar(bool theoryAtom = false);

  void markUnremovable(SatLiteral lit); 
 
  void interrupt();

  SatLiteralValue solve();
  SatLiteralValue solve(long unsigned int&);
  SatLiteralValue solve(const context::CDList<SatLiteral> & assumptions);
  void getUnsatCore(SatClause& unsatCore); 
  
  SatLiteralValue value(SatLiteral l);
  SatLiteralValue modelValue(SatLiteral l);


  void unregisterVar(SatLiteral lit);
  void renewVar(SatLiteral lit, int level = -1);
  int getAssertionLevel() const;

  // helper methods for converting from the internal Minisat representation

  static SatVariable     toSatVariable(BVMinisat::Var var); 
  static BVMinisat::Lit    toMinisatLit(SatLiteral lit);
  static SatLiteral      toSatLiteral(BVMinisat::Lit lit);
  static SatLiteralValue toSatLiteralValue(bool res);
  static SatLiteralValue toSatLiteralValue(BVMinisat::lbool res);
 
  static void  toMinisatClause(SatClause& clause, BVMinisat::vec<BVMinisat::Lit>& minisat_clause);
  static void  toSatClause    (BVMinisat::vec<BVMinisat::Lit>& clause, SatClause& sat_clause); 


  class Statistics {
  public:
    ReferenceStat<uint64_t> d_statStarts, d_statDecisions;
    ReferenceStat<uint64_t> d_statRndDecisions, d_statPropagations;
    ReferenceStat<uint64_t> d_statConflicts, d_statClausesLiterals;
    ReferenceStat<uint64_t> d_statLearntsLiterals,  d_statMaxLiterals;
    ReferenceStat<uint64_t> d_statTotLiterals;
    ReferenceStat<int> d_statEliminatedVars;
    Statistics() :
      d_statStarts("theory::bv::bvminisat::starts"),
      d_statDecisions("theory::bv::bvminisat::decisions"),
      d_statRndDecisions("theory::bv::bvminisat::rnd_decisions"),
      d_statPropagations("theory::bv::bvminisat::propagations"),
      d_statConflicts("theory::bv::bvminisat::conflicts"),
      d_statClausesLiterals("theory::bv::bvminisat::clauses_literals"),
      d_statLearntsLiterals("theory::bv::bvminisat::learnts_literals"),
      d_statMaxLiterals("theory::bv::bvminisat::max_literals"),
      d_statTotLiterals("theory::bv::bvminisat::tot_literals"),
      d_statEliminatedVars("theory::bv::bvminisat::eliminated_vars")
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
      StatisticsRegistry::registerStat(&d_statEliminatedVars);
    }
    ~Statistics() {
      StatisticsRegistry::unregisterStat(&d_statStarts);
      StatisticsRegistry::unregisterStat(&d_statDecisions);
      StatisticsRegistry::unregisterStat(&d_statRndDecisions);
      StatisticsRegistry::unregisterStat(&d_statPropagations);
      StatisticsRegistry::unregisterStat(&d_statConflicts);
      StatisticsRegistry::unregisterStat(&d_statClausesLiterals);
      StatisticsRegistry::unregisterStat(&d_statLearntsLiterals);
      StatisticsRegistry::unregisterStat(&d_statMaxLiterals);
      StatisticsRegistry::unregisterStat(&d_statTotLiterals);
      StatisticsRegistry::unregisterStat(&d_statEliminatedVars);
    }
    
    void init(BVMinisat::SimpSolver* minisat){
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
  };
  
  Statistics d_statistics;
  friend class SatSolverFactory;
}; 


// class PicosatSatSolver: public SatSolverInterface {
  
// public:
//   PicosatSatSolver();
  
//   void addClause(SatClause& clause, bool removable);

//   SatVariable newVar(bool theoryAtom = false);

//   void markUnremovable(SatLiteral lit); 
  
//   SatLiteralValue solve(unsigned long& resource = 0);
  
//   SatLiteralValue solve(const std::vector<SatLiteral>& assumptions); 

//   void interrupt();

//   SatLiteralValue value(SatLiteral l);

//   SatLiteralValue modelValue(SatLiteral l);
  
// };



class DPLLMinisatSatSolver : public DPLLSatSolverInterface {

  /** The SatSolver used */
  Minisat::SimpSolver* d_minisat;
  

  /** The SatSolver uses this to communicate with the theories */ 
  TheoryProxy* d_theoryProxy;

  /** Context we will be using to synchronzie the sat solver */
  context::Context* d_context;

  DPLLMinisatSatSolver ();
  
public:

  ~DPLLMinisatSatSolver(); 
  static SatVariable     toSatVariable(Minisat::Var var); 
  static Minisat::Lit    toMinisatLit(SatLiteral lit);
  static SatLiteral      toSatLiteral(Minisat::Lit lit);
  static SatLiteralValue toSatLiteralValue(bool res);
  static SatLiteralValue toSatLiteralValue(Minisat::lbool res);
 
  static void  toMinisatClause(SatClause& clause, Minisat::vec<Minisat::Lit>& minisat_clause);
  static void  toSatClause    (Minisat::vec<Minisat::Lit>& clause, SatClause& sat_clause); 
  
  void initialize(context::Context* context, TheoryProxy* theoryProxy); 
  
  void addClause(SatClause& clause, bool removable);

  SatVariable newVar(bool theoryAtom = false);

  SatLiteralValue solve();
  SatLiteralValue solve(long unsigned int&); 

  void interrupt();

  SatLiteralValue value(SatLiteral l);

  SatLiteralValue modelValue(SatLiteral l);

  /** Incremental interface */ 
  
  int getAssertionLevel() const;
  
  void push();

  void pop();

  void unregisterVar(SatLiteral lit);

  void renewVar(SatLiteral lit, int level = -1);

  class Statistics {
  private:
    ReferenceStat<uint64_t> d_statStarts, d_statDecisions;
    ReferenceStat<uint64_t> d_statRndDecisions, d_statPropagations;
    ReferenceStat<uint64_t> d_statConflicts, d_statClausesLiterals;
    ReferenceStat<uint64_t> d_statLearntsLiterals,  d_statMaxLiterals;
    ReferenceStat<uint64_t> d_statTotLiterals;
  public:
    Statistics() :
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
    ~Statistics() {
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
    void init(Minisat::SimpSolver* d_minisat){
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
  };
  Statistics d_statistics;

  friend class SatSolverFactory;   
}; 

class SatSolverFactory {
public:
  static  MinisatSatSolver*      createMinisat();
  static  DPLLMinisatSatSolver*  createDPLLMinisat(); 
  //static  PicosatSatSolver*      createPicosat();
  //static  DPLLPicosatSatSolver*      createDPLLPicosat(context::Context* context); 
}; 

}/* prop namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PROP__SAT_MODULE_H */
