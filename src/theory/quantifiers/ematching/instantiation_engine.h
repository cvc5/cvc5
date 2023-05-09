/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Instantiation Engine classes.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H
#define CVC5__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H

#include <vector>

#include "theory/quantifiers/ematching/inst_strategy.h"
#include "theory/quantifiers/ematching/trigger_database.h"
#include "theory/quantifiers/quant_module.h"
#include "theory/quantifiers/quant_relevance.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class InstStrategyUserPatterns;
class InstStrategyAutoGenTriggers;

class InstantiationEngine : public QuantifiersModule {
 public:
  InstantiationEngine(Env& env,
                      QuantifiersState& qs,
                      QuantifiersInferenceManager& qim,
                      QuantifiersRegistry& qr,
                      TermRegistry& tr);
  ~InstantiationEngine();
  void presolve() override;
  bool needsCheck(Theory::Effort e) override;
  void reset_round(Theory::Effort e) override;
  void check(Theory::Effort e, QEffort quant_e) override;
  bool checkCompleteFor(Node q) override;
  void checkOwnership(Node q) override;
  void registerQuantifier(Node q) override;
  /** add user pattern */
  void addUserPattern(Node q, Node pat);
  void addUserNoPattern(Node q, Node pat);
  /** Identify this module */
  std::string identify() const override;

 private:
  /** do instantiation round */
  void doInstantiationRound(Theory::Effort effort);
  /** Return true if this module should process quantified formula q */
  bool shouldProcess(Node q);
  /** instantiation strategies */
  std::vector<InstStrategy*> d_instStrategies;
  /** user-pattern instantiation strategy */
  std::unique_ptr<InstStrategyUserPatterns> d_isup;
  /** auto gen triggers; only kept for destructor cleanup */
  std::unique_ptr<InstStrategyAutoGenTriggers> d_i_ag;
  /** current processing quantified formulas */
  std::vector<Node> d_quants;
  /** all triggers will be stored in this database */
  inst::TriggerDatabase d_trdb;
  /** for computing relevance of quantifiers */
  std::unique_ptr<QuantRelevance> d_quant_rel;
}; /* class InstantiationEngine */

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H */
