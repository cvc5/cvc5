/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model-based quantifier instantiation
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__MODEL_ORACLE_H
#define CVC5__THEORY__QUANTIFIERS__MODEL_ORACLE_H

#include <map>
#include <unordered_map>

#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/** InstStrategyMbqi
 *
 */
class InstStrategyMbqi : public QuantifiersModule
{
 public:
  InstStrategyMbqi(Env& env,
                   QuantifiersState& qs,
                   QuantifiersInferenceManager& qim,
                   QuantifiersRegistry& qr,
                   TermRegistry& tr);
  ~InstStrategyMbqi() {}
  /** reset round */
  void reset_round(Theory::Effort e) override;
  /** needs check */
  bool needsCheck(Theory::Effort e) override;
  /** needs model */
  QEffort needsModel(Theory::Effort e) override;
  /** check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Check was complete for quantified formula q */
  bool checkCompleteFor(Node q) override;
  /** identify */
  std::string identify() const override { return "InstStrategyMbqi"; }

 private:
  /** process quantified formula q */
  void process(Node q);
  /** convert to query */
  Node convert(const std::vector<Node>& vars,
               Node t,
               bool toQuery,
               std::unordered_map<Node, Node>& cmap,
               std::map<TypeNode, std::unordered_set<Node> >& freshVarType,
               const std::map<Node, Node>& mvToFreshVar);
  /** The quantified formulas that we succeeded in checking */
  std::unordered_set<Node> d_quantChecked;
  /** Kinds that cannot appear in queries */
  std::unordered_set<Kind, kind::KindHashFunction> d_nonClosedKinds;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__MODEL_ORACLE_H */
