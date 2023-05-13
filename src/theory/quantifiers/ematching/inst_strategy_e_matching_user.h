/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The user-provided E-matching instantiation strategy.
 */

#include "cvc5_private.h"

#ifndef CVC5__INST_STRATEGY_E_MATCHING_USER_H
#define CVC5__INST_STRATEGY_E_MATCHING_USER_H

#include <map>
#include "expr/node.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/ematching/inst_strategy.h"
#include "theory/quantifiers/ematching/trigger.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * This class is responsible for adding instantiations based on user-provided
 * triggers.
 */
class InstStrategyUserPatterns : public InstStrategy
{
 public:
  InstStrategyUserPatterns(Env& env,
                           inst::TriggerDatabase& td,
                           QuantifiersState& qs,
                           QuantifiersInferenceManager& qim,
                           QuantifiersRegistry& qr,
                           TermRegistry& tr);
  ~InstStrategyUserPatterns();
  /** add pattern */
  void addUserPattern(Node q, Node pat);
  /** identify */
  std::string identify() const override;

 private:
  /** reset instantiation round for the given effort */
  void processResetInstantiationRound(Theory::Effort effort) override;
  /** Process quantified formula q at the given effort */
  InstStrategyStatus process(Node f, Theory::Effort effort, int e) override;
  /** explicitly provided patterns */
  std::map<Node, std::vector<inst::Trigger*> > d_user_gen;
  /** waiting to be generated patterns */
  std::map<Node, std::vector<std::vector<Node> > > d_user_gen_wait;
  /** counter for quantifiers */
  std::map<Node, int> d_counter;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
