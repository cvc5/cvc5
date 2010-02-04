/*********************                                           -*- C++ -*-  */
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
#include "prop/minisat/simp/SimpSolver.h"
#include "prop/minisat/core/SolverTypes.h"
#include "util/result.h"

#include <map>
#include "prop/cnf_stream.h"

namespace CVC4 {
  namespace prop {
    class CnfStream;
  }

  class Options;
}

namespace CVC4 {

// In terms of abstraction, this is below (and provides services to)
// Prover and above (and requires the services of) a specific
// propositional solver, DPLL or otherwise.

class PropEngine {
  const Options *d_opts;
  DecisionEngine &d_de;
  TheoryEngine &d_te;

  friend class CVC4::prop::CnfStream;
  
  /**
   * The SAT solver.
   */
  CVC4::prop::minisat::Solver* d_sat;

  std::map<Node, CVC4::prop::minisat::Var> d_atom2var;
  std::map<CVC4::prop::minisat::Var, Node> d_var2atom;


  /** 
   * Requests a fresh variable from d_sat, v.
   * Adds mapping of n -> v to d_node2var, and
   * a mapping of v -> n to d_var2node.
   */
  CVC4::prop::minisat::Var registerAtom(const Node & n);

  /**
   * Requests a fresh variable from d_sat.
   */
  CVC4::prop::minisat::Var requestFreshVar();


  /**
   * Returns true iff this Node is in the atom to variable mapping.
   * @param n the Node to lookup
   * @return true iff this Node is in the atom to variable mapping.
   */
  bool isAtomMapped(const Node & n) const;

  /**
   * Returns the variable mapped by the atom Node.
   * @param n the atom to do the lookup by
   * @return the corresponding variable
   */
  CVC4::prop::minisat::Var lookupAtom(const Node & n) const;

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
   * Returns true iff the minisat var has been mapped to an atom.
   * @param v variable to check if it is mapped
   * @return returns true iff the minisat var has been mapped.
   */
  bool isVarMapped(CVC4::prop::minisat::Var v) const;

  /**
   * Returns the atom mapped by the variable v.
   * @param v the variable to do the lookup by
   * @return an atom
   */
  Node lookupVar(CVC4::prop::minisat::Var v) const;



  /**
   * Asserts an internally constructed clause. 
   * Each literal is assumed to be in the 1:1 mapping contained in d_node2lit & d_lit2node.
   * @param c the clause to be asserted.
   */
  void assertClause(CVC4::prop::minisat::vec<CVC4::prop::minisat::Lit> & c);

  
  /** The CNF converter in use */
  CVC4::prop::CnfStream *d_cnfStream;


  void assertLit(CVC4::prop::minisat::Lit l);
  void signalBooleanPropHasEnded();

public:


  /**
   * Create a PropEngine with a particular decision and theory engine.
   */
  CVC4_PUBLIC PropEngine(const CVC4::Options* opts,
                         CVC4::DecisionEngine&,
                         CVC4::TheoryEngine&);
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


inline bool PropEngine::isAtomMapped(const Node & n) const{
  return d_atom2var.find(n) != d_atom2var.end();
}

inline CVC4::prop::minisat::Var PropEngine::lookupAtom(const Node & n) const{
  Assert(isAtomMapped(n));
  return d_atom2var.find(n)->second;
}

inline bool PropEngine::isVarMapped(CVC4::prop::minisat::Var v) const {
  return d_var2atom.find(v) != d_var2atom.end();
}

inline Node PropEngine::lookupVar(CVC4::prop::minisat::Var v) const {
  Assert(isVarMapped(v));
  return d_var2atom.find(v)->second;
}

}/* CVC4 namespace */

#endif /* __CVC4__PROP_ENGINE_H */
