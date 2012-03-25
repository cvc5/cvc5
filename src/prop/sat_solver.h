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
#include "context/cdlist.h"

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

class SatSolver {
public:  
  /** Virtual destructor to make g++ happy */
  virtual ~SatSolver() { }
  
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


class BVSatSolverInterface: public SatSolver {
public:
  virtual SatLiteralValue solve(const context::CDList<SatLiteral> & assumptions) = 0;

  virtual void markUnremovable(SatLiteral lit) = 0;

  virtual void getUnsatCore(SatClause& unsatCore) = 0; 
}; 


class DPLLSatSolverInterface: public SatSolver {
public:
  virtual void initialize(context::Context* context, prop::TheoryProxy* theoryProxy) = 0; 
  
  virtual void push() = 0;

  virtual void pop() = 0;

  virtual bool properExplanation(SatLiteral lit, SatLiteral expl) const = 0;

}; 

class SatSolverFactory {
public:
  static  BVSatSolverInterface*      createMinisat();
  static  DPLLSatSolverInterface*  createDPLLMinisat();
}; 

}/* prop namespace */

inline std::ostream& operator <<(std::ostream& out, prop::SatLiteral lit) {
  out << lit.toString();
  return out;
}

inline std::ostream& operator <<(std::ostream& out, const prop::SatClause& clause) {
  out << "clause:";
  for(unsigned i = 0; i < clause.size(); ++i) {
    out << " " << clause[i];
  }
  out << ";";
  return out;
}

inline std::ostream& operator <<(std::ostream& out, prop::SatLiteralValue val) {
  std::string str;
  switch(val) {
  case prop::SatValUnknown:
    str = "_";
    break;
  case prop::SatValTrue:
    str = "1";
    break;
  case prop::SatValFalse:
    str = "0";
    break;
  default:
    str = "Error";
    break;
  }

  out << str;
  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__PROP__SAT_MODULE_H */
