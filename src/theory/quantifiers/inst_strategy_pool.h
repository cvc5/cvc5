/*********************                                                        */
/*! \file inst_strategy_pool.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumerative instantiation
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__INST_STRATEGY_POOL_H
#define CVC4__THEORY__QUANTIFIERS__INST_STRATEGY_POOL_H

#include "theory/quantifiers/quant_module.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class RelevantDomain;

/**
 * Pool-based instantiation.
 */
class InstStrategyPool : public QuantifiersModule
{
 public:
  InstStrategyPool(QuantifiersEngine* qe,
                   QuantifiersState& qs,
                   QuantifiersInferenceManager& qim,
                   QuantifiersRegistry& qr,
                   RelevantDomain* rd);
  ~InstStrategyPool() {}
  /** Presolve */
  void presolve() override;
  /** Needs check. */
  bool needsCheck(Theory::Effort e) override;
  /** Reset round. */
  void reset_round(Theory::Effort e) override;
  /** Register quantified formula q */
  void registerQuantifier(Node q) override;
  /** Check.
   * Adds instantiations for all currently asserted
   * quantified formulas via calls to process(...)
   */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Identify. */
  std::string identify() const override
  {
    return std::string("InstStrategyPool");
  }

 private:
  /** Process quantified formula with user pool */
  void process(Node q, Node p);
  /** Map from quantified formulas to user pools */
  std::map<Node, std::vector<Node> > d_userPools;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
