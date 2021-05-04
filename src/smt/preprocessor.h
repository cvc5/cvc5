/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Justin Xu
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The preprocessor of the SmtEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PREPROCESSOR_H
#define CVC5__SMT__PREPROCESSOR_H

#include <memory>

#include "smt/expand_definitions.h"
#include "smt/process_assertions.h"
#include "theory/booleans/circuit_propagator.h"

namespace cvc5 {
class Env;
namespace preprocessing {
class PreprocessingPassContext;
}
namespace smt {

class AbstractValues;
class PreprocessProofGenerator;

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
  Preprocessor(SmtEngine& smt,
               Env& env,
               AbstractValues& abs,
               SmtEngineStatistics& stats);
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
   * @return The simplified term.
   */
  Node simplify(const Node& n);
  /**
   * Expand the definitions in a term or formula n.  No other
   * simplification or normalization is done.
   *
   * @param n The node to expand
   * @return The expanded term.
   */
  Node expandDefinitions(const Node& n);
  /** Same as above, with a cache of previous results. */
  Node expandDefinitions(
      const Node& n, std::unordered_map<Node, Node, NodeHashFunction>& cache);
  /**
   * Set proof node manager. Enables proofs in this preprocessor.
   */
  void setProofGenerator(PreprocessProofGenerator* pppg);

 private:
  /** Reference to the parent SmtEngine */
  SmtEngine& d_smt;
  /** Reference to the env */
  Env& d_env;
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
  /** Expand definitions module, responsible for expanding definitions */
  ExpandDefs d_exDefs;
  /**
   * Process assertions module, responsible for implementing the preprocessing
   * passes.
   */
  ProcessAssertions d_processor;
  /** Proof node manager */
  ProofNodeManager* d_pnm;
};

}  // namespace smt
}  // namespace cvc5

#endif
