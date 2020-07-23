/*********************                                                        */
/*! \file assertions_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for managing assertions for an SMT engine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__ASSERTIONS_MANAGER_H
#define CVC4__SMT__ASSERTIONS_MANAGER_H

#include <map>

#include "smt/process_assertions.h"
#include "smt/abstract_values.h"

namespace CVC4 {

class SmtEngine;

namespace smt {

/**
 * Module in charge of assertions for an SMT engine.
 */
class AssertionsManager
{
  /** The type of our internal map of defined functions */
  typedef context::CDHashMap<Node, smt::DefinedFunction, NodeHashFunction>
      DefinedFunctionMap;
  /** The type of our internal assertion list */
  typedef context::CDList<Node> AssertionList;
  /** The type of our internal assignment set */
  typedef context::CDHashSet<Node, NodeHashFunction> AssignmentSet;
 public:
   AssertionsManager(SmtEngine& smt, ResourceManager& rm);
  ~AssertionsManager();
  /** Process a user push.*/
  void notifyPush() ;
  /**
    * Process a user pop.  Clears out the non-context-dependent stuff in this
    * SmtEnginePrivate.  Necessary to clear out our assertion vectors in case
    * someone does a push-assert-pop without a check-sat. It also pops the
    * last map of expression names from notifyPush.
    */
  void notifyPop();
  Node applySubstitutions(TNode node);
  /** Return true if given expression is a defined function. */
  bool isDefinedFunction(Node func);

  /**
   * Simplify node "in" by expanding definitions and applying any
   * substitutions learned from preprocessing.
   */
  Node simplify(TNode in);

  /**
   * Adds a formula to the current context.  Action here depends on
   * the SimplificationMode (in the current Options scope); the
   * formula might be pushed out to the propositional layer
   * immediately, or it might be simplified and kept, or it might not
   * even be simplified.
   * The arguments isInput and isAssumption are used for bookkeeping for proofs.
   * The argument maybeHasFv should be set to true if the assertion may have
   * free variables. By construction, assertions from the smt2 parser are
   * guaranteed not to have free variables. However, other cases such as
   * assertions from the SyGuS parser may have free variables (say if the
   * input contains an assert or define-fun-rec command).
   *
   * @param isAssumption If true, the formula is considered to be an assumption
   * (this is used to distinguish assertions and assumptions)
   */
  void addFormula(
    TNode n, bool inUnsatCore, bool inInput, bool isAssumption, bool maybeHasFv);
  /** finish init */
  void finishInit();
  /** get ite skolem map */
  IteSkolemMap& getIteSkolemMap() { return d_assertions.getIteSkolemMap(); }
  ProcessAssertions* getProcessAssertions() { return &d_processor; }
 private:
  /** Reference to the SMT engine */
  SmtEngine& d_smt;
  /** Reference to resource manager */
  ResourceManager& d_resourceManager;
  /** The assertions processor */
  ProcessAssertions d_proc;
  /** The abstract values utility */
  std::unique_ptr<smt::AbstractValues> d_absValues;
  /** An index of our defined functions */
  DefinedFunctionMap* d_definedFunctions;
  /**
   * The assertion list (before any conversion) for supporting
   * getAssertions().  Only maintained if in incremental mode.
   */
  AssertionList* d_assertionList;

  /**
   * List of lemmas generated for global recursive function definitions. We
   * assert this list of definitions in each check-sat call.
   */
  std::unique_ptr<std::vector<Node>> d_globalDefineFunRecLemmas;

  /**
   * The list of assumptions from the previous call to checkSatisfiability.
   * Note that if the last call to checkSatisfiability was an entailment check,
   * i.e., a call to checkEntailed(a1, ..., an), then d_assumptions contains
   * one single assumption ~(a1 AND ... AND an).
   */
  std::vector<Node> d_assumptions;
  /**
   * List of items for which to retrieve values using getAssignment().
   */
  AssignmentSet* d_assignments;
  /*
   * Whether we did a global negation of the formula.
   */
  bool d_globalNegation;
  /** Assertions in the preprocessing pipeline */
  AssertionPipeline d_assertions;
  /** Whether any assertions have been processed */
  CDO<bool> d_assertionsProcessed;
  /** Instance of the ITE remover */
  RemoveTermFormulas d_iteRemover;

  /** The preprocessing pass context */
  std::unique_ptr<PreprocessingPassContext> d_preprocessingPassContext;
};

}  // namespace smt
}  // namespace CVC4

#endif
