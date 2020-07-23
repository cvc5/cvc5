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
  /** The type of our internal assertion list */
  typedef context::CDList<Node> AssertionList;
  /** The type of our internal assignment set */
  typedef context::CDHashSet<Node, NodeHashFunction> AssignmentSet;
 public:
   AssertionsManager(SmtEngine& smt);
  ~AssertionsManager();
  /** finish init */
  void finishInit();
  /** Process a user push.*/
  void notifyPush();
  /**
    * Process a user pop.  Clears out the non-context-dependent stuff in this
    * SmtEnginePrivate.  Necessary to clear out our assertion vectors in case
    * someone does a push-assert-pop without a check-sat. It also pops the
    * last map of expression names from notifyPush.
    */
  void notifyPop();
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
  /** Get assumptions */
  std::vector<Node>& getAssumptions();
 private:
  /** Reference to the SMT engine */
  SmtEngine& d_smt;
  /**
   * The assertion list (before any conversion) for supporting
   * getAssertions().  Only maintained if in incremental mode.
   */
  AssertionList* d_assertionList;

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
};

}  // namespace smt
}  // namespace CVC4

#endif
