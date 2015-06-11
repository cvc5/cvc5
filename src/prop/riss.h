/*********************                                                        */
/*! \file glucose.h
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
 ** Implementation of the glucose sat solver for cvc4 (bitvectors).
 **/

#include "cvc4_private.h"

#pragma once

#include "prop/sat_solver.h"

#ifdef CVC4_USE_RISS

#include <riss/core/Solver.h>
#include <coprocessor/Coprocessor.h>

namespace CVC4 {
namespace prop {

class RissSolver : public SatSolver {

private:
  Riss::CoreConfig d_config;
  Coprocessor::CP3Config d_CP3Config;
  Riss::Solver* d_solver;
  SatVariable d_true;
  SatVariable d_false;
   
public:
  RissSolver(const std::string& name = "");
  ~RissSolver() throw(AssertionException);

  void addClause(SatClause& clause, bool removable, uint64_t proof_id);
  void addXorClause(SatClause& clause, bool rhs, bool removable, uint64_t proof_id) {
    Unreachable();
  }

  bool nativeXor() { return false; }
  
  SatVariable newVar(bool isTheoryAtom = false, bool preRegister = false, bool canErase = true);

  SatVariable trueVar();
  SatVariable falseVar();

  void markUnremovable(SatLiteral lit);

  void interrupt();
  
  SatValue solve();
  SatValue solve(long unsigned int&);
  SatValue value(SatLiteral l);
  SatValue modelValue(SatLiteral l);
  unsigned getAssertionLevel() const;


  // helper methods for converting from the internal representation

  static SatVariable toSatVariable(Riss::Var var);
  static Riss::Lit toInternalLit(SatLiteral lit);
  static SatLiteral toSatLiteral(Riss::Lit lit);
  static SatValue toSatLiteralValue(bool res);
  static SatValue toSatLiteralValue(Riss::lbool res);

  static void  toInternalClause(SatClause& clause, Riss::vec<Riss::Lit>& internal_clause);
  static void  toSatClause (Riss::vec<Riss::Lit>& clause, SatClause& sat_clause);

  class Statistics {
  public:
    IntStat d_statCallsToSolve;
    IntStat d_xorClausesAdded;
    IntStat d_clausesAdded;
    TimerStat d_solveTime;
    bool d_registerStats;
    Statistics(const std::string& prefix);
    ~Statistics();
  };

  Statistics d_statistics;
};

}
}

#else // CVC4_USE_RISS

namespace CVC4 {
namespace prop {

class RissSolver : public SatSolver {

public:
  RissSolver(const std::string& name = "") { Unreachable(); }
  /** Assert a clause in the solver. */
  void addClause(SatClause& clause, bool removable, uint64_t proof_id) {
    Unreachable();
  }

  /** Return true if the solver supports native xor resoning */
  bool nativeXor() { Unreachable(); }

  /** Add a clause corresponding to rhs = l1 xor .. xor ln  */
  void addXorClause(SatClause& clause, bool rhs, bool removable, uint64_t proof_id) {
    Unreachable();
  }
  
  SatVariable newVar(bool isTheoryAtom, bool preRegister, bool canErase) { Unreachable(); }
  SatVariable trueVar() { Unreachable(); }
  SatVariable falseVar() { Unreachable(); }
  SatValue solve() { Unreachable(); }
  SatValue solve(long unsigned int&) { Unreachable(); }
  void interrupt() { Unreachable(); }
  SatValue value(SatLiteral l) { Unreachable(); }
  SatValue modelValue(SatLiteral l) { Unreachable(); }
  unsigned getAssertionLevel() const { Unreachable(); }

};/* class RissSolver */
} // CVC4::prop
} // CVC4

#endif // CVC4_USE_RISS



