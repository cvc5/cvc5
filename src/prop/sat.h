/*********************                                                        */
/** sat.h
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): cconway
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

#ifndef __CVC4__PROP__SAT_H
#define __CVC4__PROP__SAT_H

// Just defining this for now, since there's no other SAT solver bindings.
// Optional blocks below will be unconditionally included
#define __CVC4_USE_MINISAT

#include "util/options.h"

#ifdef __CVC4_USE_MINISAT

#include "prop/minisat/core/Solver.h"
#include "prop/minisat/core/SolverTypes.h"
#include "prop/minisat/simp/SimpSolver.h"

#endif /* __CVC4_USE_MINISAT */

namespace CVC4 {

class TheoryEngine;

namespace prop {

class PropEngine;
class CnfStream;

/* Definitions of abstract types and conversion functions for SAT interface */

#ifdef __CVC4_USE_MINISAT

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

static inline size_t
hashSatLiteral(const SatLiteral& literal) {
  return (size_t) minisat::toInt(literal);
}

#endif /* __CVC4_USE_MINISAT */

/** Interface encapsulating the "input" to the solver, e.g., from the 
 * CNF converter. 
 * 
 * TODO: Is it possible to push the typedefs of SatClause and SatVariable
 * into here, somehow?
 */
class SatInputInterface {
public:
  /** Assert a clause in the solver. */
  virtual void addClause(SatClause& clause) = 0;
  /** Create a new boolean variable in the solver. */
  virtual SatVariable newVar(bool theoryAtom = false) = 0;
};

/**
 * The proxy class that allows us to modify the internals of the SAT solver.
 * It's only accessible from the PropEngine, and should be treated with major
 * care.
 */
class SatSolver : public SatInputInterface {

  /** The prop engine we are using */
  PropEngine* d_propEngine;

  /** The CNF engine we are using */
  CnfStream* d_cnfStream;

  /** The theory engine we are using */
  TheoryEngine* d_theoryEngine;

  /** Context we will be using to synchronzie the sat solver */
  context::Context* d_context;

  /** Remember the options */
  Options* d_options;
  
  /* Pointer to the concrete SAT solver. Including this via the
     preprocessor saves us a level of indirection vs, e.g., defining a
     sub-class for each solver. */

#ifdef __CVC4_USE_MINISAT

  /** Minisat solver */
  minisat::SimpSolver* d_minisat;

#endif /* __CVC4_USE_MINISAT */

protected:

public:
  /** Hash function for literals */
  struct SatLiteralHashFunction {
    inline size_t operator()(const SatLiteral& literal) const;
  };

  SatSolver(PropEngine* propEngine,
                   TheoryEngine* theoryEngine,
                   context::Context* context,
                   const Options* options);

  ~SatSolver();

  bool solve();
  
  void addClause(SatClause& clause);

  SatVariable newVar(bool theoryAtom = false);

  void theoryCheck(SatClause& conflict);

  void enqueueTheoryLiteral(const SatLiteral& l);
  
  void setCnfStream(CnfStream* cnfStream);
};

/* Functions that delegate to the concrete SAT solver. */

#ifdef __CVC4_USE_MINISAT

inline SatSolver::SatSolver(PropEngine* propEngine, TheoryEngine* theoryEngine,
                     context::Context* context, const Options* options) :
  d_propEngine(propEngine),
  d_cnfStream(NULL),
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

inline SatSolver::~SatSolver() {
  delete d_minisat;
}

inline bool SatSolver::solve() {
  return d_minisat->solve();
}

inline void SatSolver::addClause(SatClause& clause) {
  d_minisat->addClause(clause);
}

inline SatVariable SatSolver::newVar(bool theoryAtom) {
  return d_minisat->newVar(true, true, theoryAtom);
}

#endif /* __CVC4_USE_MINISAT */

inline size_t
SatSolver::SatLiteralHashFunction::operator()(const SatLiteral& literal) const {
  return hashSatLiteral(literal);
}

inline std::ostream& operator <<(std::ostream& out, SatLiteral lit) {
  const char * s = (literalSign(lit)) ? "~" : " ";
  out << s << literalToVariable(lit);
  return out;
}

inline std::ostream& operator <<(std::ostream& out, const SatClause& clause) {
  out << "clause:";
  for(int i = 0; i < clause.size(); ++i) {
    out << " " << clause[i];
  }
  out << ";";
  return out;
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PROP__SAT_H */
