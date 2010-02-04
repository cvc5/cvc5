/*********************                                                        */
/** sat.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** SAT Solver.
 **/

#ifndef __CVC4__PROP__SAT_H
#define __CVC4__PROP__SAT_H

#define __CVC4_USE_MINISAT

#ifdef __CVC4_USE_MINISAT

#include "prop/minisat/core/Solver.h"
#include "prop/minisat/core/SolverTypes.h"

namespace CVC4 {
namespace prop {

/** The solver we are using */
typedef minisat::Solver SatSolver;

/** Type of the SAT variables */
typedef minisat::Var SatVariable;

/** Type of the Sat literals */
typedef minisat::Lit SatLiteral;

/** Type of the SAT clauses */
typedef minisat::vec<SatLiteral> SatClause;

/**
 * Returns the variable of the literal.
 * @param lit the literal
 */
inline SatVariable literalToVariable(SatLiteral lit) {
  return minisat::var(lit);
}

inline bool literalSign(SatLiteral lit) {
  return minisat::sign(lit);
}

inline std::ostream& operator << (std::ostream& out, SatLiteral lit) {
  const char * s = (literalSign(lit)) ? "~" : " ";
  out << s << literalToVariable(lit);
  return out;
}

inline std::ostream& operator << (std::ostream& out, const SatClause& clause) {
  out << "clause:";
  for(int i = 0; i < clause.size(); ++i) {
    out << " " << clause[i];
  }
  out << ";";
  return out;
}


}/* CVC4::prop namespace */
}/* CVC4 namespace */

#endif


#endif /* __CVC4__PROP__SAT_H */
