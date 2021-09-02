/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The preprocessing pass context for passes
 *
 * Implementation of the preprocessing pass context for passes. This context
 * allows preprocessing passes to retrieve information besides the assertions
 * from the solver and interact with it without getting full access.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PREPROCESSING_PASS_CONTEXT_H
#define CVC5__PREPROCESSING__PREPROCESSING_PASS_CONTEXT_H

#include "context/cdhashset.h"
#include "preprocessing/learned_literal_manager.h"
#include "theory/logic_info.h"
#include "util/resource_manager.h"

namespace cvc5 {

class Env;
class SmtEngine;
class TheoryEngine;

namespace theory {
class Rewriter;
}

namespace theory::booleans {
class CircuitPropagator;
}

namespace prop {
class PropEngine;
}

namespace preprocessing {

class PreprocessingPassContext
{
 public:
  /** Constructor. */
  PreprocessingPassContext(
      SmtEngine* smt,
      Env& env,
      theory::booleans::CircuitPropagator* circuitPropagator);

  /** Get the associated SmtEngine. */
  SmtEngine* getSmt() const { return d_smt; }

  /** Get the associated TheoryEngine. */
  TheoryEngine* getTheoryEngine() const;
  /** Get the associated Propengine. */
  prop::PropEngine* getPropEngine() const;
  /** Get the current user context. */
  context::Context* getUserContext() const;
  /** Get the current decision context. */
  context::Context* getDecisionContext() const;

  /** Get the associated circuit propagator. */
  theory::booleans::CircuitPropagator* getCircuitPropagator() const
  {
    return d_circuitPropagator;
  }

  /**
   * Get the (user-context-dependent) set of symbols that occur in at least one
   * assertion in the current user context.
   */
  const context::CDHashSet<Node>& getSymsInAssertions() const
  {
    return d_symsInAssertions;
  }

  /** Spend resource in the resource manager of the associated Env. */
  void spendResource(Resource r);

  /** Get the options of the environment */
  const Options& getOptions() const;
  /** Get the current logic info of the environment */
  const LogicInfo& getLogicInfo() const;

  /** Get a pointer to the Rewriter owned by the associated Env. */
  theory::Rewriter* getRewriter() const;

  /** Get a reference to the top-level substitution map */
  theory::TrustSubstitutionMap& getTopLevelSubstitutions() const;

  /** Record symbols in assertions
   *
   * This method is called when a set of assertions is finalized. It adds
   * the symbols to d_symsInAssertions that occur in assertions.
   */
  void recordSymbolsInAssertions(const std::vector<Node>& assertions);

  /**
   * Notify learned literal. This method is called when a literal is
   * entailed by the current set of assertions.
   *
   * It should be rewritten, and such that top level substitutions have
   * been applied to it.
   */
  void notifyLearnedLiteral(TNode lit);
  /**
   * Get the learned literals
   */
  std::vector<Node> getLearnedLiterals() const;
  /**
   * Add substitution to the top-level substitutions, which also as a
   * consequence is used by the theory model.
   * @param lhs The node replaced by node 'rhs'
   * @param rhs The node to substitute node 'lhs'
   * @param pg The proof generator that can provide a proof of lhs == rhs.
   */
  void addSubstitution(const Node& lhs,
                       const Node& rhs,
                       ProofGenerator* pg = nullptr);
  /** Same as above, with proof id */
  void addSubstitution(const Node& lhs,
                       const Node& rhs,
                       PfRule id,
                       const std::vector<Node>& args);

  /** The the proof node manager associated with this context, if it exists */
  ProofNodeManager* getProofNodeManager() const;

 private:
  /** Pointer to the SmtEngine that this context was created in. */
  SmtEngine* d_smt;
  /** Reference to the environment. */
  Env& d_env;
  /** Instance of the circuit propagator */
  theory::booleans::CircuitPropagator* d_circuitPropagator;
  /**
   * The learned literal manager
   */
  LearnedLiteralManager d_llm;

  /**
   * The (user-context-dependent) set of symbols that occur in at least one
   * assertion in the current user context.
   */
  context::CDHashSet<Node> d_symsInAssertions;

};  // class PreprocessingPassContext

}  // namespace preprocessing
}  // namespace cvc5

#endif /* CVC5__PREPROCESSING__PREPROCESSING_PASS_CONTEXT_H */
