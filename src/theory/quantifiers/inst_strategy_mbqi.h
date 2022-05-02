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
  InstStrategyMbqi( Env& env,
                   QuantifiersState& qs,
                   QuantifiersInferenceManager& qim,
                   QuantifiersRegistry& qr,
                   TermRegistry& tr);
  ~InstStrategyMbqi(){}
  /** reset round */
  void reset_round( Theory::Effort e ) override;
  /** needs check */
  bool needsCheck(Theory::Effort e) override;
  /** needs model */
  QEffort needsModel(Theory::Effort e) override;
  /** check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Check was complete for quantified formula q */
  bool checkCompleteFor( Node q ) override;
  /** identify */
  std::string identify() const override { return "InstStrategyMbqi"; }
 private:
  /** check success */
  bool d_check_success;
  /** clean model value 
   * 
   * 
   */
  Node cleanModelValue( Node n, std::unordered_map<TNode, Node> visited);
  /** map from terms to fresh variables */
  std::unordered_map< Node, Node > d_fresh_var;
  /** get or make fresh variable for */
  Node getOrMkFreshVariableFor(Node c);
  /** list of fresh variables per type */
  std::map< TypeNode, std::vector< Node > > d_fresh_var_type;
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC5__THEORY__QUANTIFIERS__MODEL_ORACLE_H */
