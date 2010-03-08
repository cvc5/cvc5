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

#ifndef __CVC4__PROP__SAT_H
#define __CVC4__PROP__SAT_H

#include "cvc4_private.h"

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
class CnfStream;

/** Type of the SAT variables */
typedef minisat::Var SatVariable;

/** Type of the Sat literals */
typedef minisat::Lit SatLiteral;

/** Type of the SAT clauses */
typedef minisat::vec<SatLiteral> SatClause;

/**
 * The proxy class that allows us to modify the internals of the SAT solver.
 * It's only accessible from the PropEngine, and should be treated with major
 * care.
 */
class SatSolver {

  /** The prop engine we are using */
  PropEngine* d_propEngine;

  /** The CNF engine we are using */
  CnfStream* d_cnfStream;

  /** The theory engine we are using */
  TheoryEngine* d_theoryEngine;

  /** Context we will be using to synchronzie the sat solver */
  context::Context* d_context;

  /** Minisat solver */
  minisat::SimpSolver* d_minisat;

  /** Remember the options */
  Options* d_options;

public:

  /** Hash function for literals */
  struct SatLiteralHashFcn {
    inline size_t operator()(const SatLiteral& literal) const;
  };

  inline SatSolver(PropEngine* propEngine, TheoryEngine* theoryEngine, context::Context* context,
            const Options* options);

  inline ~SatSolver();

  inline bool solve();

  inline void addClause(SatClause& clause);

  inline SatVariable newVar(bool theoryAtom = false);

  inline void theoryCheck(SatClause& conflict);

  inline void enqueueTheoryLiteral(const SatLiteral& l);

  inline void setCnfStream(CnfStream* cnfStream);
};

}/* CVC4::prop namespace */
}/* CVC4 namespace */

#include "context/context.h"
#include "theory/theory_engine.h"
#include "prop/prop_engine.h"
#include "prop/cnf_stream.h"

namespace CVC4 {
namespace prop {

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

size_t SatSolver::SatLiteralHashFcn::operator()(const SatLiteral& literal) const {
  return (size_t) minisat::toInt(literal);
}

SatSolver::SatSolver(PropEngine* propEngine, TheoryEngine* theoryEngine,
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

SatSolver::~SatSolver() {
  delete d_minisat;
}

bool SatSolver::solve() {
  return d_minisat->solve();
}

void SatSolver::addClause(SatClause& clause) {
  d_minisat->addClause(clause);
}

SatVariable SatSolver::newVar(bool theoryAtom) {
  return d_minisat->newVar(true, true, theoryAtom);
}

void SatSolver::theoryCheck(SatClause& conflict) {
  // Run the thoery checks
  d_theoryEngine->check(theory::Theory::FULL_EFFORT);
  // Try to get the conflict
  Node conflictNode = d_theoryEngine->getConflict();
  // If the conflict is there, construct the conflict clause
  if (!conflictNode.isNull()) {
    Debug("prop") << "SatSolver::theoryCheck() => conflict" << std::endl;
    Node::const_iterator literal_it = conflictNode.begin();
    Node::const_iterator literal_end = conflictNode.end();
    while (literal_it != literal_end) {
      // Get the node and construct it's negation
      Node literalNode = (*literal_it);
      Node negated = literalNode.getKind() == kind::NOT ? literalNode[0] : literalNode.notNode();
      // Get the literal corresponding to the node
      SatLiteral l = d_cnfStream->getLiteral(negated);
      // Add to the conflict clause and continue
      conflict.push(l);
      literal_it ++;
    }
  }
}

void SatSolver::enqueueTheoryLiteral(const SatLiteral& l) {
  Node literalNode = d_cnfStream->getNode(l);
  // We can get null from the prop engine if the literal is useless (i.e.)
  // the expression is not in context anyomore
  if(!literalNode.isNull()) {
    d_theoryEngine->assertFact(literalNode);
  }
}

void SatSolver::setCnfStream(CnfStream* cnfStream) {
  d_cnfStream = cnfStream;
}


}/* CVC4::prop namespace */
}/* CVC4 namespace */

#endif

#endif /* __CVC4__PROP__SAT_H */
