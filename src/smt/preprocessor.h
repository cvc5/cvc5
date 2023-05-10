/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Justin Xu
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The preprocessor of the SolverEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PREPROCESSOR_H
#define CVC5__SMT__PREPROCESSOR_H

#include <memory>

#include "smt/env_obj.h"
#include "smt/process_assertions.h"
#include "theory/booleans/circuit_propagator.h"

namespace cvc5::internal {

class TheoryEngine;

namespace preprocessing {
class PreprocessingPassContext;
}
namespace prop {
class PropEngine;
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
class Preprocessor : protected EnvObj
{
 public:
  Preprocessor(Env& env, SolverEngineStatistics& stats);
  ~Preprocessor();
  /**
   * Finish initialization
   */
  void finishInit(TheoryEngine* te, prop::PropEngine* pe);
  /**
   * Process the assertions that have been asserted in argument as. Returns
   * true if no conflict was discovered while preprocessing them.
   *
   * @param ap The assertions to preprocess
   */
  bool process(preprocessing::AssertionPipeline& ap);
  /**
   * Clear learned literals from the Boolean propagator.
   */
  void clearLearnedLiterals();
  /** Get learned literals */
  std::vector<Node> getLearnedLiterals() const;
  /**
   * Cleanup, which deletes the processing passes owned by this module. This
   * is required to be done explicitly so that passes are deleted before the
   * objects they refer to in the SolverEngine destructor.
   */
  void cleanup();
  /**
   * Apply top-level substitutions and eliminate abstract values in a term or
   * formula n.  No other simplification or normalization is done.
   *
   * @param n The node to subsitute
   * @return The term after substitution.
   */
  Node applySubstitutions(const Node& n);
  /** Same as above, for a list of assertions, updating in place */
  void applySubstitutions(std::vector<Node>& ns);
  /** Get the preprocess proof generator */
  PreprocessProofGenerator* getPreprocessProofGenerator();

 private:
  /** The preprocess proof generator. */
  std::unique_ptr<PreprocessProofGenerator> d_pppg;
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
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
