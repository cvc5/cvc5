/*********************                                                        */
/*! \file minisat.h
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

#pragma once

#include "prop/sat_solver.h"
#include "prop/minisat/simp/SimpSolver.h"

namespace CVC4 {
namespace prop {

class MinisatSatSolver : public DPLLSatSolverInterface {

  /** The SatSolver used */
  CVC4::Minisat::SimpSolver* d_minisat;

  /** Context we will be using to synchronize the sat solver */
  context::Context* d_context;

  void setupOptions();

public:

  MinisatSatSolver();
  ~MinisatSatSolver() throw();
;

  static SatVariable     toSatVariable(CVC4::Minisat::Var var);
  static CVC4::Minisat::Lit    toMinisatLit(SatLiteral lit);
  static SatLiteral      toSatLiteral(CVC4::Minisat::Lit lit);
  static SatValue        toSatLiteralValue(CVC4::Minisat::lbool res);
  static CVC4::Minisat::lbool  toMinisatlbool(SatValue val);
  //(Commented because not in use) static bool            tobool(SatValue val);

  static void  toMinisatClause(SatClause& clause, CVC4::Minisat::vec<CVC4::Minisat::Lit>& minisat_clause);
  static void  toSatClause    (CVC4::Minisat::vec<CVC4::Minisat::Lit>& clause, SatClause& sat_clause);
  static void  toSatClause    (const CVC4::Minisat::Clause& clause, SatClause& sat_clause);
  void initialize(context::Context* context, TheoryProxy* theoryProxy);

  void addClause(SatClause& clause, bool removable, uint64_t proof_id);
  void addXorClause(SatClause& clause, bool rhs, bool removable, uint64_t proof_id) {
    Unreachable("Minisat does not support native XOR reasoning");
  }
  SatVariable newVar(bool isTheoryAtom, bool preRegister, bool canErase);
  SatVariable trueVar() { return d_minisat->trueVar(); }
  SatVariable falseVar() { return d_minisat->falseVar(); }

  SatValue solve();
  SatValue solve(long unsigned int&);

  void interrupt();

  SatValue value(SatLiteral l);

  SatValue modelValue(SatLiteral l);

  bool properExplanation(SatLiteral lit, SatLiteral expl) const;

  /** Incremental interface */

  unsigned getAssertionLevel() const;

  void push();

  void pop();

  void requirePhase(SatLiteral lit);

  bool flipDecision();

  bool isDecision(SatVariable decn) const;

  class Statistics {
  private:
    ReferenceStat<uint64_t> d_statStarts, d_statDecisions;
    ReferenceStat<uint64_t> d_statRndDecisions, d_statPropagations;
    ReferenceStat<uint64_t> d_statConflicts, d_statClausesLiterals;
    ReferenceStat<uint64_t> d_statLearntsLiterals,  d_statMaxLiterals;
    ReferenceStat<uint64_t> d_statTotLiterals;
  public:
    Statistics();
    ~Statistics();
    void init(CVC4::Minisat::SimpSolver* d_minisat);
  };/* class MinisatSatSolver::Statistics */
  Statistics d_statistics;

};/* class MinisatSatSolver */

}/* CVC4::prop namespace */
}/* CVC4 namespace */
