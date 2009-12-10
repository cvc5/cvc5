/*********************                                           -*- C++ -*-  */
/** prop_engine.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#ifndef __CVC4__PROP_ENGINE_H
#define __CVC4__PROP_ENGINE_H

#include "cvc4_config.h"
#include "expr/node.h"
#include "util/decision_engine.h"
#include "theory/theory_engine.h"
#include "prop/minisat/simp/SimpSolver.h"
#include "prop/minisat/core/SolverTypes.h"

#include <map>

namespace CVC4 {

// In terms of abstraction, this is below (and provides services to)
// Prover and above (and requires the services of) a specific
// propositional solver, DPLL or otherwise.

class PropEngine {
  DecisionEngine &d_de;
  TheoryEngine &d_te;
  CVC4::prop::minisat::SimpSolver d_sat;
  std::map<Node, CVC4::prop::minisat::Var> d_vars;
  std::map<CVC4::prop::minisat::Var, Node> d_varsReverse;

  void addVars(Node);

public:
  /**
   * Create a PropEngine with a particular decision and theory engine.
   */
  CVC4_PUBLIC PropEngine(CVC4::DecisionEngine&, CVC4::TheoryEngine&);

  /**
   * Converts to CNF if necessary.
   */
  void solve(Node);

};/* class PropEngine */

}/* CVC4 namespace */

#endif /* __CVC4__PROP_ENGINE_H */
