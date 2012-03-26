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

#include "cvc4_public.h"

#ifndef __CVC4__PROP__SAT_MODULE_H
#define __CVC4__PROP__SAT_MODULE_H

#include <stdint.h> 
#include "util/options.h"
#include "util/stats.h"
#include "context/cdlist.h"

namespace CVC4 {
namespace prop {

class TheoryProxy; 

/**
 * Boolean values of the SAT solver.
 */
enum SatValue {
  SAT_VALUE_UNKNOWN,
  SAT_VALUE_TRUE, 
  SAT_VALUE_FALSE 
};

/**
 * A variable of the SAT solver.
 */
typedef uint64_t SatVariable; 

/**
 * Undefined SAT solver variable.
 */
const SatVariable undefSatVariable = SatVariable(-1); 

/**
 * A SAT literal is a variable or an negated variable.
 */
class SatLiteral {

  /**
   * The value holds the variable and a bit noting if the variable is negated.
   */
  uint64_t d_value;

public:

  /**
   * Construct an undefined SAT literal.
   */
  SatLiteral()
  : d_value(undefSatVariable)
  {}
  
  /**
   * Construct a literal given a possible negated variable.
   */
  SatLiteral(SatVariable var, bool negated = false) {
    d_value = var + var + (int)negated;
  }

  /**
   * Returns the variable of the literal.
   */
  SatVariable getSatVariable() const {
    return d_value >> 1;
  }

  /**
   * Returns true if the literal is a negated variable.
   */
  bool isNegated() const {
    return d_value & 1;
  }

  /**
   * Negate the given literal.
   */
  SatLiteral operator ~ () const {
    return SatLiteral(getSatVariable(), !isNegated()); 
  }

  /**
   * Compare two literals for equality.
   */
  bool operator == (const SatLiteral& other) const {
    return d_value == other.d_value; 
  }

  /**
   * Compare two literals for dis-equality.
   */
  bool operator != (const SatLiteral& other) const {
    return !(*this == other); 
  }

  /**
   * Returns a string representation of the literal.
   */
  std::string toString() const {
    std::ostringstream os;
    os << (isNegated()? "~" : "") << getSatVariable() << " ";
    return os.str();
  }

  /**
   * Returns the hash value of a literal.
   */
  size_t hash() const {
    return (size_t)d_value;
  }

  /**
   * Returns true if the literal is undefined.
   */
  bool isNull() const {
    return getSatVariable() == undefSatVariable;
  }
};

/**
 * A constant representing a undefined literal.
 */
const SatLiteral undefSatLiteral = SatLiteral(undefSatVariable);  

/**
 * Helper for hashing the literals.
 */
struct SatLiteralHashFunction {
  inline size_t operator() (const SatLiteral& literal) const {
    return literal.hash();
  }
};

/**
 * A SAT clause is a vector of literals.
 */
typedef std::vector<SatLiteral> SatClause;

class SatSolver {

public:  

  /** Virtual destructor */
  virtual ~SatSolver() { }
  
  /** Assert a clause in the solver. */
  virtual void addClause(SatClause& clause, bool removable) = 0;

  /** Create a new boolean variable in the solver. */
  virtual SatVariable newVar(bool theoryAtom = false) = 0;

 
  /** Check the satisfiability of the added clauses */
  virtual SatValue solve() = 0;

  /** Check the satisfiability of the added clauses */
  virtual SatValue solve(long unsigned int&) = 0;
  
  /** Interrupt the solver */
  virtual void interrupt() = 0;

  /** Call value() during the search.*/
  virtual SatValue value(SatLiteral l) = 0;

  /** Call modelValue() when the search is done.*/
  virtual SatValue modelValue(SatLiteral l) = 0;

  virtual void unregisterVar(SatLiteral lit) = 0;
  
  virtual void renewVar(SatLiteral lit, int level = -1) = 0;

  virtual unsigned getAssertionLevel() const = 0;

};


class BVSatSolverInterface: public SatSolver {
public:
  virtual SatValue solve(const context::CDList<SatLiteral> & assumptions) = 0;

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

inline std::ostream& operator <<(std::ostream& out, prop::SatValue val) {
  std::string str;
  switch(val) {
  case prop::SAT_VALUE_UNKNOWN:
    str = "_";
    break;
  case prop::SAT_VALUE_TRUE:
    str = "1";
    break;
  case prop::SAT_VALUE_FALSE:
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
