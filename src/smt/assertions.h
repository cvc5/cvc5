/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for storing assertions for an SMT engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__ASSERTIONS_H
#define CVC5__SMT__ASSERTIONS_H

#include <vector>

#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "preprocessing/assertion_pipeline.h"
#include "smt/env_obj.h"

namespace cvc5 {
namespace smt {

class AbstractValues;

/**
 * Contains all information pertaining to the assertions of an SMT engine.
 *
 * This class is responsible for setting up the assertions pipeline for
 * check-sat calls. It is *not* responsible for the preprocessing itself, and
 * instead is intended to be the input to a preprocessor utility.
 */
class Assertions : protected EnvObj
{
  /** The type of our internal assertion list */
  typedef context::CDList<Node> AssertionList;

 public:
  Assertions(Env& env, AbstractValues& absv);
  ~Assertions();
  /**
   * Clears out the non-context-dependent data in this class.  Necessary to
   * clear out our assertion vectors in case someone does a push-assert-pop
   * without a check-sat.
   */
  void clearCurrent();
  /** refresh
   *
   * Ensures that all global declarations have been processed in the current
   * context. This may trigger substitutions to be added to the top-level
   * substitution and/or formulas added to the current set of assertions.
   *
   * If global declarations are true, this method must be called before
   * processing assertions.
   */
  void refresh();
  /*
   * Initialize a call to check satisfiability. This adds assumptions to
   * the list of assumptions maintained by this class, and finalizes the
   * set of formulas (in the assertions pipeline) that will be used for the
   * upcoming check-sat call.
   *
   * @param assumptions The assumptions of the upcoming check-sat call.
   * @param isEntailmentCheck Whether we are checking entailment of assumptions
   * in the upcoming check-sat call.
   */
  void initializeCheckSat(const std::vector<Node>& assumptions,
                          bool isEntailmentCheck);
  /**
   * Add a formula to the current context: preprocess, do per-theory
   * setup, use processAssertionList(), asserting to T-solver for
   * literals and conjunction of literals.  Returns false if
   * immediately determined to be inconsistent.
   *
   * @throw TypeCheckingException, LogicException
   */
  void assertFormula(const Node& n);
  /**
   * Assert that n corresponds to an assertion from a define-fun or
   * define-fun-rec command.
   * This assertion is added to the set of assertions maintained by this class.
   * If this has a global definition, this assertion is persistent for any
   * subsequent check-sat calls.
   */
  void addDefineFunDefinition(Node n, bool global);
  /**
   * Get the assertions pipeline, which contains the set of assertions we are
   * currently processing.
   */
  preprocessing::AssertionPipeline& getAssertionPipeline();
  /**
   * Get assertions list corresponding to the original list of assertions,
   * before preprocessing. This includes assertions corresponding to define-fun
   * and define-fun-rec.
   */
  const context::CDList<Node>& getAssertionList() const;
  /**
   * Get assertions list corresponding to the original list of assertions
   * that correspond to definitions (define-fun or define-fun-rec).
   */
  const context::CDList<Node>& getAssertionListDefinitions() const;
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
  /**
   * Enable proofs for this assertions class. This must be called
   * explicitly since we construct the assertions before we know
   * whether proofs are enabled.
   *
   * @param pppg The preprocess proof generator of the proof manager.
   */
  void enableProofs(smt::PreprocessProofGenerator* pppg);
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
                  bool isAssumption,
                  bool isFunDef,
                  bool maybeHasFv);
  /** Reference to the abstract values utility */
  AbstractValues& d_absValues;
  /**
   * The assertion list (before any conversion) for supporting getAssertions().
   */
  AssertionList d_assertionList;
  /** The subset of above the correspond to define-fun or define-fun-rec */
  AssertionList d_assertionListDefs;
  /**
   * List of lemmas generated for global (recursive) function definitions. We
   * assert this list of definitions in each check-sat call.
   */
  std::vector<Node> d_globalDefineFunLemmas;
  /** The index of the above list that we have processed */
  context::CDO<size_t> d_globalDefineFunLemmasIndex;
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
}  // namespace cvc5

#endif
