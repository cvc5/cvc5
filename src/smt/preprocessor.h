/*********************                                                        */
/*! \file preprocessor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessor of the SmtEngine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__PREPROCESSOR_H
#define CVC4__SMT__PREPROCESSOR_H

#include <vector>

#include "preprocessing/preprocessing_pass_context.h"
#include "smt/process_assertions.h"
#include "smt/term_formula_removal.h"
#include "theory/booleans/circuit_propagator.h"

namespace CVC4 {
namespace smt {

class AbstractValues;

/**
 * The preprocessor module of an SMT engine.
 *
 * This class is responsible for:
 * (1) preprocessing the set of assertions from input before they are sent to
 * the SMT solver,
 * (2) implementing methods for expanding and simplifying formulas. The latter
 * takes into account the substitutions inferred by this class.
 */
class Preprocessor
{
 public:
  Preprocessor(SmtEngine& smt, context::UserContext* u, AbstractValues& abs);
  ~Preprocessor();
  /**
   * Finish initialization
   */
  void finishInit();
  /**
   * Process the assertions that have been asserted in argument as. Returns
   * true if no conflict was discovered while preprocessing them.
   */
  bool process(Assertions& as);
  /**
   * Postprocess assertions, called after the SmtEngine has finished
   * giving the assertions to the SMT solver and before the assertions are
   * cleared.
   */
  void postprocess(Assertions& as);
  /**
   * Clear learned literals from the Boolean propagator.
   */
  void clearLearnedLiterals();
  /**
   * Cleanup, which deletes the processing passes owned by this module. This
   * is required to be done explicitly so that passes are deleted before the
   * objects they refer to in the SmtEngine destructor.
   */
  void cleanup();
  /**
   * Simplify a formula without doing "much" work.  Does not involve
   * the SAT Engine in the simplification, but uses the current
   * definitions, assertions, and the current partial model, if one
   * has been constructed.  It also involves theory normalization.
   *
   * @param n The node to simplify
   * @param removeItes Whether to remove ITE (and other terms with formulas in
   * term positions) from the result.
   * @return The simplified term.
   */
  Node simplify(const Node& n, bool removeItes = false);
  /**
   * Expand the definitions in a term or formula n.  No other
   * simplification or normalization is done.
   *
   * @param n The node to expand
   * @param expandOnly if true, then the expandDefinitions function of
   * TheoryEngine is not called on subterms of n.
   * @return The expanded term.
   */
  Node expandDefinitions(const Node& n, bool expandOnly = false);
  /** Same as above, with a cache of previous results. */
  Node expandDefinitions(
      const Node& n,
      std::unordered_map<Node, Node, NodeHashFunction>& cache,
      bool expandOnly = false);
  /**
   * Get the underlying term formula remover utility.
   */
  RemoveTermFormulas& getTermFormulaRemover();

 private:
  /**
   * Apply substitutions that have been inferred by preprocessing, return the
   * substituted form of node.
   */
  Node applySubstitutions(TNode node);
  /** Reference to the parent SmtEngine */
  SmtEngine& d_smt;
  /** Reference to the abstract values utility */
  AbstractValues& d_absValues;
  /**
   * A circuit propagator for non-clausal propositional deduction.
   */
  theory::booleans::CircuitPropagator d_propagator;
  /**
   * User-context-dependent flag of whether any assertions have been processed.
   */
  context::CDO<bool> d_assertionsProcessed;
  /** The preprocessing pass context */
  std::unique_ptr<preprocessing::PreprocessingPassContext> d_ppContext;
  /**
   * Process assertions module, responsible for implementing the preprocessing
   * passes.
   */
  ProcessAssertions d_processor;
  /**
   * The term formula remover, responsible for eliminating formulas that occur
   * in term contexts.
   */
  RemoveTermFormulas d_rtf;
};

}  // namespace smt
}  // namespace CVC4

#endif
