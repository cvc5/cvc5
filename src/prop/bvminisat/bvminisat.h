/*********************                                                        */
/*! \file bvminisat.h
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
 ** Implementation of the minisat for cvc4 (bitvectors).
 **/

#pragma once

#include "prop/sat_solver.h"
#include "prop/sat_solver_registry.h"
#include "prop/bvminisat/simp/SimpSolver.h"

namespace CVC4 {
namespace prop {

class BVMinisatSatSolver: public BVSatSolverInterface {
  BVMinisat::SimpSolver* d_minisat;

public:
  BVMinisatSatSolver();
  ~BVMinisatSatSolver();
  void addClause(SatClause& clause, bool removable);

  SatVariable newVar(bool theoryAtom = false);

  void markUnremovable(SatLiteral lit);

  void interrupt();

  SatValue solve();
  SatValue solve(long unsigned int&);
  SatValue solve(const context::CDList<SatLiteral> & assumptions);
  void getUnsatCore(SatClause& unsatCore);

  SatValue value(SatLiteral l);
  SatValue modelValue(SatLiteral l);

  void unregisterVar(SatLiteral lit);
  void renewVar(SatLiteral lit, int level = -1);
  unsigned getAssertionLevel() const;


  // helper methods for converting from the internal Minisat representation

  static SatVariable     toSatVariable(BVMinisat::Var var);
  static BVMinisat::Lit    toMinisatLit(SatLiteral lit);
  static SatLiteral      toSatLiteral(BVMinisat::Lit lit);
  static SatValue toSatLiteralValue(bool res);
  static SatValue toSatLiteralValue(BVMinisat::lbool res);

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
    Statistics();
    ~Statistics();
    void init(BVMinisat::SimpSolver* minisat);
  };

  Statistics d_statistics;
};

template class SatSolverConstructor<BVMinisatSatSolver>;

}
}




