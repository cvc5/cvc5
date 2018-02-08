/*********************                                                        */
/*! \file cryptominisat.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** Implementation of the cryptominisat sat solver for cvc4 (bitvectors).
 **/

#include "cvc4_private.h"

#pragma once

#include "prop/sat_solver.h"

#ifdef CVC4_USE_CRYPTOMINISAT
#include <cryptominisat4/cryptominisat.h>
namespace CVC4 {
namespace prop {

class CryptoMinisatSolver : public SatSolver {

private:
  CMSat::SATSolver* d_solver;
  unsigned d_numVariables;
  bool d_okay;
  SatVariable d_true;
  SatVariable d_false;
public:
  CryptoMinisatSolver(StatisticsRegistry* registry,
                      const std::string& name = "");
  virtual ~CryptoMinisatSolver();

  ClauseId addClause(SatClause& clause, bool removable);
  ClauseId addXorClause(SatClause& clause, bool rhs, bool removable);

  bool nativeXor() { return true; }
  
  SatVariable newVar(bool isTheoryAtom = false, bool preRegister = false, bool canErase = true);

  SatVariable trueVar();
  SatVariable falseVar();

  void markUnremovable(SatLiteral lit);

  void interrupt();
  
  SatValue solve();
  SatValue solve(long unsigned int&);
  bool ok() const;
  SatValue value(SatLiteral l);
  SatValue modelValue(SatLiteral l);

  unsigned getAssertionLevel() const;


  // helper methods for converting from the internal Minisat representation

  static SatVariable toSatVariable(CMSat::Var var);
  static CMSat::Lit toInternalLit(SatLiteral lit);
  static SatLiteral toSatLiteral(CMSat::Lit lit);
  static SatValue toSatLiteralValue(bool res);
  static SatValue toSatLiteralValue(CMSat::lbool res);

  static void  toInternalClause(SatClause& clause, std::vector<CMSat::Lit>& internal_clause);
  static void  toSatClause (std::vector<CMSat::Lit>& clause, SatClause& sat_clause);

  class Statistics {
  public:
    StatisticsRegistry* d_registry;
    IntStat d_statCallsToSolve;
    IntStat d_xorClausesAdded;
    IntStat d_clausesAdded;
    TimerStat d_solveTime;
    bool d_registerStats;
    Statistics(StatisticsRegistry* registry,
               const std::string& prefix);
    ~Statistics();
  };

  Statistics d_statistics;
};

}  // namespace prop
}  // namespace CVC4
#endif  // CVC4_USE_CRYPTOMINISAT
