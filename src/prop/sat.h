/*********************                                                        */
/** sat.h
 ** Original author: mdeters
 ** Major contributors: dejan
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

#include "cvc4_private.h"
#include "context/context.h"
#include "theory/theory_engine.h"

#ifndef __CVC4__PROP__SAT_H
#define __CVC4__PROP__SAT_H

#define __CVC4_USE_MINISAT

#ifdef __CVC4_USE_MINISAT

#include "util/options.h"
#include "prop/minisat/core/Solver.h"
#include "prop/minisat/core/SolverTypes.h"
#include "prop/minisat/simp/SimpSolver.h"

namespace CVC4 {

class TheoryEngine;

namespace prop {

class PropEngine;

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

/**
 * The proxy class that allows us to modify the internals of the SAT solver.
 * It's only accessible from the PropEngine, and should be treated with major
 * care.
 */
class SatSolver {

  /** The prop engine we are using */
  PropEngine* d_propEngine;

  /** The theory engine we are using */
  TheoryEngine* d_theoryEngine;

  /** Context we will be using to synchronzie the sat solver */
  context::Context* d_context;

  /** Minisat solver */
  minisat::SimpSolver* d_minisat;

  /** Remember the options */
  Options* d_options;

  public:

    SatSolver(PropEngine* propEngine, TheoryEngine* theoryEngine,
                   context::Context* context, const Options* options)
      : d_propEngine(propEngine),
        d_theoryEngine(theoryEngine),
        d_context(context)
    {
      // Create the solver
      d_minisat = new minisat::SimpSolver(this, d_context);
      // Setup the verbosity
      d_minisat->verbosity = (options->verbosity > 0) ? 1 : -1;
      // Do not delete the satisfied clauses, just the learnt ones
      d_minisat->remove_satisfied = false;
      // Make minisat reuse the literal values
      d_minisat->polarity_mode = minisat::SimpSolver::polarity_user;
    }

    ~SatSolver() {
      delete d_minisat;
    }

    inline bool solve() {
      return d_minisat->solve();
    }

    inline void addClause(SatClause& clause) {
      d_minisat->addClause(clause);
    }

    inline SatVariable newVar() {
      return d_minisat->newVar();
    }

    inline void theoryCheck(SatClause& conflict) {
    }
};



}/* CVC4::prop namespace */
}/* CVC4 namespace */

#endif


#endif /* __CVC4__PROP__SAT_H */
