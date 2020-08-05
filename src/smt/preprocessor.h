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
   * Cleanup
   */
  void cleanup();
  /**
   * Simplify a formula without doing "much" work.  Does not involve
   * the SAT Engine in the simplification, but uses the current
   * definitions, assertions, and the current partial model, if one
   * has been constructed.  It also involves theory normalization.
   *
   * @throw TypeCheckingException, LogicException, UnsafeInterruptException
   *
   * @todo (design) is this meant to give an equivalent or an
   * equisatisfiable formula?
   */
  Node simplify(const Node& e, bool removeItes = false);
  /** Same as above, with a cache */
  Node simplify(const Node& e, std::unordered_map<Node, Node, NodeHashFunction>& cache, bool removeItes = false);
  /**
   * Expand the definitions in a term or formula.  No other
   * simplification or normalization is done.
   *
   * @throw TypeCheckingException, LogicException, UnsafeInterruptException
   */
  Node expandDefinitions(const Node& e);
  /** Same as above, with a cache */
  Node expandDefinitions(const Node& e, 
  std::unordered_map<Node, Node, NodeHashFunction>& cache);
  /**
   * Get term formula remover
   */
  RemoveTermFormulas& getTermFormulaRemover();

 private:
  /** 
   * Apply substitutions that have been inferred by preprocessing, return the
   * substituted form of node.
   */
  Node applySubstitutions(TNode node)
  /** Reference to the parent SmtEngine */
  SmtEngine& d_smt;
  /** Reference to the abstract values utility */
  AbstractValues& d_absValues;
  /** 
   * A circuit propagator for non-clausal propositional deduction 
   */
  theory::booleans::CircuitPropagator d_propagator;
  /** 
   * User-context-dependent flag of whether any assertions have been processed 
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
