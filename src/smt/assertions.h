/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace smt {

class AbstractValues;
class PreprocessProofGenerator;

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
  Assertions(Env& env);
  ~Assertions();
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
   */
  void setAssumptions(const std::vector<Node>& assumptions);
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
  /** Get the set corresponding to the above */
  std::unordered_set<Node> getCurrentAssertionListDefitions() const;
  /**
   * Get the list of assumptions, which are those registered to this class
   * on initializeCheckSat.
   */
  std::vector<Node>& getAssumptions();
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
   */
  void addFormula(TNode n,
                  bool isFunDef,
                  bool maybeHasFv);
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
   */
  std::vector<Node> d_assumptions;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
