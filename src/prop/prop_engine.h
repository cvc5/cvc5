/*********************                                                        */
/*! \file prop_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The PropEngine (propositional engine); main interface point
 ** between CVC4's SMT infrastructure and the SAT solver
 **
 ** The PropEngine (propositional engine); main interface point
 ** between CVC4's SMT infrastructure and the SAT solver.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROP_ENGINE_H
#define CVC4__PROP_ENGINE_H

#include <sys/time.h>

#include "base/modal_exception.h"
#include "expr/node.h"
#include "options/options.h"
#include "preprocessing/assertion_pipeline.h"
#include "proof/proof_manager.h"
#include "util/resource_manager.h"
#include "util/result.h"
#include "util/unsafe_interrupt_exception.h"

namespace CVC4 {

class ResourceManager;
class DecisionEngine;
class TheoryEngine;

namespace theory {
  class TheoryRegistrar;
}/* CVC4::theory namespace */

namespace prop {

class CnfStream;
class DPLLSatSolverInterface;

class PropEngine;

/**
 * PropEngine is the abstraction of a Sat Solver, providing methods for
 * solving the SAT problem and conversion to CNF (via the CnfStream).
 */
class PropEngine
{
 public:
  /**
   * Create a PropEngine with a particular decision and theory engine.
   */
  PropEngine(TheoryEngine*,
             context::Context* satContext,
             context::UserContext* userContext,
             ResourceManager* rm);

  /**
   * Destructor.
   */
  CVC4_PUBLIC ~PropEngine();

  /**
   * Finish initialize. Call this after construction just before we are
   * ready to use this class. Should be called after TheoryEngine::finishInit.
   * This method converts and asserts true and false into the CNF stream.
   */
  void finishInit();

  /**
   * This is called by SmtEngine, at shutdown time, just before
   * destruction.  It is important because there are destruction
   * ordering issues between some parts of the system (notably between
   * PropEngine and Theory).  For now, there's nothing to do here in
   * the PropEngine.
   */
  void shutdown() {}

  /**
   * Converts the given formula to CNF and assert the CNF to the SAT solver.
   * The formula is asserted permanently for the current context.
   * @param node the formula to assert
   */
  void assertFormula(TNode node);

  /**
   * Converts the given formula to CNF and assert the CNF to the SAT solver.
   * The formula can be removed by the SAT solver after backtracking lower
   * than the (SAT and SMT) level at which it was asserted.
   *
   * @param node the formula to assert
   * @param negated whether the node should be considered to be negated
   * at the top level (or not)
   * @param removable whether this lemma can be quietly removed based
   * on an activity heuristic (or not)
   */
  void assertLemma(TNode node, bool negated, bool removable);

  /**
   * Pass a list of assertions from an AssertionPipeline to the decision engine.
   */
  void addAssertionsToDecisionEngine(
      const preprocessing::AssertionPipeline& assertions);

  /**
   * If ever n is decided upon, it must be in the given phase.  This
   * occurs *globally*, i.e., even if the literal is untranslated by
   * user pop and retranslated, it keeps this phase.  The associated
   * variable will _always_ be phase-locked.
   *
   * @param n the node in question; must have an associated SAT literal
   * @param phase the phase to use
   */
  void requirePhase(TNode n, bool phase);

  /**
   * Return whether the given literal is a SAT decision.  Either phase
   * is permitted; that is, if "lit" is a SAT decision, this function
   * returns true for both lit and the negation of lit.
   */
  bool isDecision(Node lit) const;

  /**
   * Checks the current context for satisfiability.
   *
   */
  Result checkSat();

  /**
   * Get the value of a boolean variable.
   *
   * @return mkConst<true>, mkConst<false>, or Node::null() if
   * unassigned.
   */
  Node getValue(TNode node) const;

  /**
   * Return true if node has an associated SAT literal.
   */
  bool isSatLiteral(TNode node) const;

  /**
   * Check if the node has a value and return it if yes.
   */
  bool hasValue(TNode node, bool& value) const;

  /**
   * Returns the Boolean variables known to the SAT solver.
   */
  void getBooleanVariables(std::vector<TNode>& outputVariables) const;

  /**
   * Ensure that the given node will have a designated SAT literal
   * that is definitionally equal to it.  The result of this function
   * is that the Node can be queried via getSatValue().
   */
  void ensureLiteral(TNode n);

  /**
   * Push the context level.
   */
  void push();

  /**
   * Pop the context level.
   */
  void pop();

  /*
   * Reset the decisions in the DPLL(T) SAT solver at the current assertion
   * level.
   */
  void resetTrail();

  /**
   * Get the assertion level of the SAT solver.
   */
  unsigned getAssertionLevel() const;

  /**
   * Return true if we are currently searching (either in this or
   * another thread).
   */
  bool isRunning() const;

  /**
   * Interrupt a running solver (cause a timeout).
   *
   * Can potentially throw a ModalException.
   */
  void interrupt();

  /**
   * Informs the ResourceManager that a resource has been spent.  If out of
   * resources, can throw an UnsafeInterruptException exception.
   */
  void spendResource(ResourceManager::Resource r);

  /**
   * For debugging.  Return true if "expl" is a well-formed
   * explanation for "node," meaning:
   *
   * 1. expl is either a SAT literal or an AND of SAT literals
   *    currently assigned true;
   * 2. node is assigned true;
   * 3. node does not appear in expl; and
   * 4. node was assigned after all of the literals in expl
   */
  bool properExplanation(TNode node, TNode expl) const;

 private:
  /** Dump out the satisfying assignment (after SAT result) */
  void printSatisfyingAssignment();
  /**
   * Indicates that the SAT solver is currently solving something and we should
   * not mess with it's internal state.
   */
  bool d_inCheckSat;

  /** The theory engine we will be using */
  TheoryEngine* d_theoryEngine;

  /** The decision engine we will be using */
  std::unique_ptr<DecisionEngine> d_decisionEngine;

  /** The context */
  context::Context* d_context;

  /** SAT solver's proxy back to theories; kept around for dtor cleanup */
  TheoryProxy* d_theoryProxy;

  /** The SAT solver proxy */
  DPLLSatSolverInterface* d_satSolver;

  /** List of all of the assertions that need to be made */
  std::vector<Node> d_assertionList;

  /** Theory registrar; kept around for destructor cleanup */
  theory::TheoryRegistrar* d_registrar;

  /** The CNF converter in use */
  CnfStream* d_cnfStream;

  /** Whether we were just interrupted (or not) */
  bool d_interrupted;
  /** Pointer to resource manager for associated SmtEngine */
  ResourceManager* d_resourceManager;

};

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP_ENGINE_H */
