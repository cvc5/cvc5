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
#include "smt/smt_engine.h"
#include "theory/trust_substitutions.h"
#include "util/resource_manager.h"

namespace cvc5 {
class SmtEngine;
class TheoryEngine;
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
  PreprocessingPassContext(
      SmtEngine* smt,
      Env& env,
      theory::booleans::CircuitPropagator* circuitPropagator);

  SmtEngine* getSmt() { return d_smt; }
  TheoryEngine* getTheoryEngine() { return d_smt->getTheoryEngine(); }
  prop::PropEngine* getPropEngine() { return d_smt->getPropEngine(); }
  context::Context* getUserContext();
  context::Context* getDecisionContext();

  theory::booleans::CircuitPropagator* getCircuitPropagator()
  {
    return d_circuitPropagator;
  }

  context::CDHashSet<Node, NodeHashFunction>& getSymsInAssertions()
  {
    return d_symsInAssertions;
  }

  void spendResource(Resource r);

  /** Get the current logic info of the SmtEngine */
  const LogicInfo& getLogicInfo() { return d_smt->getLogicInfo(); }

  /** Gets a reference to the top-level substitution map */
  theory::TrustSubstitutionMap& getTopLevelSubstitutions();

  /** Record symbols in assertions
   *
   * This method is called when a set of assertions is finalized. It adds
   * the symbols to d_symsInAssertions that occur in assertions.
   */
  void recordSymbolsInAssertions(const std::vector<Node>& assertions);

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
  ProofNodeManager* getProofNodeManager();

 private:
  /** Pointer to the SmtEngine that this context was created in. */
  SmtEngine* d_smt;
  /** Reference to the environment. */
  Env& d_env;
  /** Instance of the circuit propagator */
  theory::booleans::CircuitPropagator* d_circuitPropagator;
  /**
   * The (user-context-dependent) set of symbols that occur in at least one
   * assertion in the current user context.
   */
  context::CDHashSet<Node, NodeHashFunction> d_symsInAssertions;

};  // class PreprocessingPassContext

}  // namespace preprocessing
}  // namespace cvc5

#endif /* CVC5__PREPROCESSING__PREPROCESSING_PASS_CONTEXT_H */
