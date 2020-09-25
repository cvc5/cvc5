/*********************                                                        */
/*! \file preprocessing_pass_context.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mathias Preiner, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessing pass context for passes
 **
 ** Implementation of the preprocessing pass context for passes. This context
 ** allows preprocessing passes to retrieve information besides the assertions
 ** from the solver and interact with it without getting full access.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PREPROCESSING_PASS_CONTEXT_H
#define CVC4__PREPROCESSING__PREPROCESSING_PASS_CONTEXT_H

#include "context/cdo.h"
#include "context/context.h"
#include "decision/decision_engine.h"
#include "preprocessing/util/ite_utilities.h"
#include "smt/smt_engine.h"
#include "smt/term_formula_removal.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/theory_engine.h"
#include "util/resource_manager.h"

namespace CVC4 {
namespace preprocessing {

class PreprocessingPassContext
{
 public:
  PreprocessingPassContext(
      SmtEngine* smt,
      RemoveTermFormulas* iteRemover,
      theory::booleans::CircuitPropagator* circuitPropagator);

  SmtEngine* getSmt() { return d_smt; }
  TheoryEngine* getTheoryEngine() { return d_smt->getTheoryEngine(); }
  prop::PropEngine* getPropEngine() { return d_smt->getPropEngine(); }
  context::Context* getUserContext() { return d_smt->getUserContext(); }
  context::Context* getDecisionContext() { return d_smt->getContext(); }
  RemoveTermFormulas* getIteRemover() { return d_iteRemover; }

  theory::booleans::CircuitPropagator* getCircuitPropagator()
  {
    return d_circuitPropagator;
  }

  context::CDHashSet<Node, NodeHashFunction>& getSymsInAssertions()
  {
    return d_symsInAssertions;
  }

  void spendResource(ResourceManager::Resource r)
  {
    d_resourceManager->spendResource(r);
  }

  const LogicInfo& getLogicInfo() { return d_smt->d_logic; }

  /* Widen the logic to include the given theory. */
  void widenLogic(theory::TheoryId id);

  /** Gets a reference to the top-level substitution map */
  theory::SubstitutionMap& getTopLevelSubstitutions()
  {
    return d_topLevelSubstitutions;
  }

  /* Enable Integers. */
  void enableIntegers();

  /** Record symbols in assertions
   *
   * This method is called when a set of assertions is finalized. It adds
   * the symbols to d_symsInAssertions that occur in assertions.
   */
  void recordSymbolsInAssertions(const std::vector<Node>& assertions);

 private:
  /** Pointer to the SmtEngine that this context was created in. */
  SmtEngine* d_smt;

  /** Pointer to the ResourceManager for this context. */
  ResourceManager* d_resourceManager;

  /** Instance of the ITE remover */
  RemoveTermFormulas* d_iteRemover;

  /* The top level substitutions */
  theory::SubstitutionMap d_topLevelSubstitutions;

  /** Instance of the circuit propagator */
  theory::booleans::CircuitPropagator* d_circuitPropagator;

  /**
   * The (user-context-dependent) set of symbols that occur in at least one
   * assertion in the current user context.
   */
  context::CDHashSet<Node, NodeHashFunction> d_symsInAssertions;

};  // class PreprocessingPassContext

}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PREPROCESSING_PASS_CONTEXT_H */
