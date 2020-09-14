/*********************                                                        */
/*! \file assertions.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for storing assertions for an SMT engine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__ASSERTIONS_H
#define CVC4__SMT__ASSERTIONS_H

#include <vector>

#include "context/cdlist.h"
#include "context/context.h"
#include "expr/node.h"
#include "preprocessing/assertion_pipeline.h"
#include "smt/abstract_values.h"

namespace CVC4 {
namespace smt {

/**
 * Contains all information pertaining to the assertions of an SMT engine.
 *
 * This class is responsible for setting up the assertions pipeline for
 * check-sat calls. It is *not* responsible for the preprocessing itself, and
 * instead is intended to be the input to a preprocessor utility.
 */
class Assertions
{
  /** The type of our internal assertion list */
  typedef context::CDList<Node> AssertionList;

 public:
  Assertions(context::UserContext* u, AbstractValues& absv);
  ~Assertions();
  /**
   * Finish initialization, called once after options are finalized. Sets up
   * the required bookkeeping based on the options.
   */
  void finishInit();
  /**
   * Clears out the non-context-dependent data in this class.  Necessary to
   * clear out our assertion vectors in case someone does a push-assert-pop
   * without a check-sat.
   */
  void clearCurrent();
  /*
   * Initialize a call to check satisfiability. This adds assumptions to
   * the list of assumptions maintained by this class, and finalizes the
   * set of formulas (in the assertions pipeline) that will be used for the
   * upcoming check-sat call.
   *
   * @param assumptions The assumptions of the upcoming check-sat call.
   * @param inUnsatCore Whether assumptions are in the unsat core.
   * @param isEntailmentCheck Whether we are checking entailment of assumptions
   * in the upcoming check-sat call.
   */
  void initializeCheckSat(const std::vector<Node>& assumptions,
                          bool inUnsatCore,
                          bool isEntailmentCheck);
  /**
   * Add a formula to the current context: preprocess, do per-theory
   * setup, use processAssertionList(), asserting to T-solver for
   * literals and conjunction of literals.  Returns false if
   * immediately determined to be inconsistent.  This version
   * takes a Boolean flag to determine whether to include this asserted
   * formula in an unsat core (if one is later requested).
   *
   * @throw TypeCheckingException, LogicException, UnsafeInterruptException
   */
  void assertFormula(const Node& n, bool inUnsatCore = true);
  /**
   * Assert that n corresponds to an assertion from a define-fun-rec command.
   * This assertion is added to the set of assertions maintained by this class.
   * If this has a global definition, this assertion is persistent for any
   * subsequent check-sat calls.
   */
  void addDefineFunRecDefinition(Node n, bool global);
  /**
   * Get the assertions pipeline, which contains the set of assertions we are
   * currently processing.
   */
  preprocessing::AssertionPipeline& getAssertionPipeline();
  /**
   * Get assertions list corresponding to the original list of assertions,
   * before preprocessing.
   */
  context::CDList<Node>* getAssertionList();
  /**
   * Get the list of assumptions, which are those registered to this class
   * on initializeCheckSat.
   */
  std::vector<Node>& getAssumptions();
  /**
   * Is the set of assertions globally negated? When this flag is true, the
   * overall result of check-sat should be inverted.
   */
  bool isGlobalNegated() const;
  /** Flip the global negation flag. */
  void flipGlobalNegated();

  //------------------------------------ for proofs
  /** Set proof generator */
  void setProofGenerator(smt::PreprocessProofGenerator* pppg);
  /** Is proof enabled? */
  bool isProofEnabled() const;
  //------------------------------------ end for proofs
 private:
  /**
   * Fully type-check the argument, and also type-check that it's
   * actually Boolean.
   * throw@ TypeCheckingException
   */
  void ensureBoolean(const Node& n);
  /**
   * Adds a formula to the current context.  Action here depends on
   * the SimplificationMode (in the current Options scope); the
   * formula might be pushed out to the propositional layer
   * immediately, or it might be simplified and kept, or it might not
   * even be simplified.
   * The arguments isInput and isAssumption are used for bookkeeping for unsat
   * cores.
   * The argument maybeHasFv should be set to true if the assertion may have
   * free variables. By construction, assertions from the smt2 parser are
   * guaranteed not to have free variables. However, other cases such as
   * assertions from the SyGuS parser may have free variables (say if the
   * input contains an assert or define-fun-rec command).
   *
   * @param isAssumption If true, the formula is considered to be an assumption
   * (this is used to distinguish assertions and assumptions)
   */
  void addFormula(TNode n,
                  bool inUnsatCore,
                  bool inInput,
                  bool isAssumption,
                  bool maybeHasFv);
  /** pointer to the user context */
  context::UserContext* d_userContext;
  /** Reference to the abstract values utility */
  AbstractValues& d_absValues;
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
  /** Whether we did a global negation of the formula. */
  bool d_globalNegation;
  /** Assertions in the preprocessing pipeline */
  preprocessing::AssertionPipeline d_assertions;
};

}  // namespace smt
}  // namespace CVC4

#endif
