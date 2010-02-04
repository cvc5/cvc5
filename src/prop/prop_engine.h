/*********************                                                        */
/** prop_engine.h
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** The PropEngine (proposiitonal engine); main interface point
 ** between CVC4's SMT infrastructure and the SAT solver.
 **/

#ifndef __CVC4__PROP_ENGINE_H
#define __CVC4__PROP_ENGINE_H

#include "cvc4_config.h"
#include "expr/node.h"
#include "util/decision_engine.h"
#include "theory/theory_engine.h"
#include "sat.h"
#include "util/result.h"
#include "util/options.h"

#include <map>

namespace CVC4 {
namespace prop {

class CnfStream;

// In terms of abstraction, this is below (and provides services to)
// Prover and above (and requires the services of) a specific
// propositional solver, DPLL or otherwise.

class PropEngine {

  friend class CnfStream;

  /** The global options */
  const Options *d_opts;
  /** The decision engine we will be using */
  DecisionEngine *d_de;
  /** The theory engine we will be using */
  TheoryEngine *d_te;

  /**
   * The SAT solver.
   */
  SatSolver* d_sat;

  std::map<Node, SatVariable> d_atom2var;
  std::map<SatVariable, Node> d_var2atom;

  /** 
   * Requests a fresh variable from d_sat, v.
   * Adds mapping of n -> v to d_node2var, and
   * a mapping of v -> n to d_var2node.
   */
  SatVariable registerAtom(const Node& node);

  /**
   * Requests a fresh variable from d_sat.
   */
  SatVariable requestFreshVar();

  /**
   * Returns true iff this Node is in the atom to variable mapping.
   * @param n the Node to lookup
   * @return true iff this Node is in the atom to variable mapping.
   */
  bool isAtomMapped(const Node& node) const;

  /**
   * Returns the variable mapped by the atom Node.
   * @param n the atom to do the lookup by
   * @return the corresponding variable
   */
  SatVariable lookupAtom(const Node& node) const;

  /**
   * Flags whether the solver may need to have its state reset before
   * solving occurs
   */
  bool d_restartMayBeNeeded;

  /**
   * Cleans existing state in the PropEngine and reinitializes the state.
   */
  void restart();

  /**
   * Keeps track of all of the assertions that need to be made.
   */
  std::vector<Node> d_assertionList;

  /**
   * Returns true iff the variable from the sat solver has been mapped to
   * an atom.
   * @param var variable to check if it is mapped
   * @return returns true iff the minisat var has been mapped.
   */
  bool isVarMapped(SatVariable var) const;

  /**
   * Returns the atom mapped by the variable v.
   * @param var the variable to do the lookup by
   * @return an atom
   */
  Node lookupVar(SatVariable var) const;

  /**
   * Asserts an internally constructed clause. Each literal is assumed to be in
   * the 1-1 mapping contained in d_node2lit and d_lit2node.
   * @param clause the clause to be asserted.
   */
  void assertClause(SatClause& clause);

  /** The CNF converter in use */
  CnfStream* d_cnfStream;

  void assertLit(SatLiteral lit);
  void signalBooleanPropHasEnded();

public:

  /**
   * Create a PropEngine with a particular decision and theory engine.
   */
  PropEngine(const Options* opts, DecisionEngine*, TheoryEngine*);

  /**
   * Destructor.
   */
  CVC4_PUBLIC ~PropEngine();

  /**
   * Converts the given formula to CNF and assert the CNF to the sat solver.
   */
  void assertFormula(const Node& node);

  /**
   * Currently this takes a well-formed* Node,
   * converts it to a propositionally equisatisifiable formula for a sat solver,
   * and invokes the sat solver for a satisfying assignment.
   * TODO: what does well-formed mean here?
   */
  Result solve();

};/* class PropEngine */

inline bool PropEngine::isAtomMapped(const Node & n) const {
  return d_atom2var.find(n) != d_atom2var.end();
}

inline SatVariable PropEngine::lookupAtom(const Node & n) const {
  Assert(isAtomMapped(n));
  return d_atom2var.find(n)->second;
}

inline bool PropEngine::isVarMapped(SatVariable v) const {
  return d_var2atom.find(v) != d_var2atom.end();
}

inline Node PropEngine::lookupVar(SatVariable v) const {
  Assert(isVarMapped(v));
  return d_var2atom.find(v)->second;
}

}/* prop namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PROP_ENGINE_H */
