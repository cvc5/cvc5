/*********************                                                        */
/*! \file sat.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking, cconway, dejan
 ** Minor contributors (to current version): barrett
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

#ifndef __CVC4__PROP__SAT_H
#define __CVC4__PROP__SAT_H

// Just defining this for now, since there's no other SAT solver bindings.
// Optional blocks below will be unconditionally included
#define __CVC4_USE_MINISAT

#include "theory/theory.h"
#include "util/options.h"
#include "util/stats.h"

#include "prop/sat_module.h"

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

/**
 * The proxy class that allows the SatSolver to communicate with the theories
 */
class TheoryProxy {

  /** The prop engine we are using */
  PropEngine* d_propEngine;

  /** The CNF engine we are using */
  CnfStream* d_cnfStream;

  /** The theory engine we are using */
  TheoryEngine* d_theoryEngine;

  /** Context we will be using to synchronzie the sat solver */
  context::Context* d_context;

  /**
   * Set of all lemmas that have been "shared" in the portfolio---i.e.,
   * all imported and exported lemmas.
   */
  std::hash_set<Node, NodeHashFunction> d_shared;

public:
  TheoryProxy(PropEngine* propEngine,
              TheoryEngine* theoryEngine,
              context::Context* context,
              CnfStream* cnfStream);

  ~TheoryProxy();


  void theoryCheck(theory::Theory::Effort effort);

  void explainPropagation(SatLiteral l, SatClause& explanation);

  void theoryPropagate(SatClause& output);

  void enqueueTheoryLiteral(const SatLiteral& l);

  SatLiteral getNextDecisionRequest();

  bool theoryNeedCheck() const;

  void removeClausesAboveLevel(int level);

  /**
   * Notifies of a new variable at a decision level.
   */
  void variableNotify(SatVariable var);

  void unregisterVar(SatLiteral lit);

  void renewVar(SatLiteral lit, int level = -1);

  TNode getNode(SatLiteral lit);

  void notifyRestart();

  void notifyNewLemma(SatClause& lemma);

  SatLiteral getNextReplayDecision();

  void logDecision(SatLiteral lit);

  void checkTime();

};/* class SatSolver */

/* Functions that delegate to the concrete SAT solver. */

inline TheoryProxy::TheoryProxy(PropEngine* propEngine,
                                TheoryEngine* theoryEngine,
                                context::Context* context,
                                CnfStream* cnfStream) :
  d_propEngine(propEngine),
  d_cnfStream(cnfStream),
  d_theoryEngine(theoryEngine),
  d_context(context)
{}

}/* CVC4::prop namespace */

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
  case prop::SatValTrue:
    str = "1";
  case prop::SatValFalse:
    str = "0";
  default:
    str = "Error"; 

  out << str;
  return out;
}

} /* prop namespace */

}/* CVC4 namespace */

#endif /* __CVC4__PROP__SAT_H */
