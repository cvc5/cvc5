/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Pool-based instantiation strategy
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_POOL_H
#define CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_POOL_H

#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Pool-based instantiation. This implements a strategy for instantiating
 * quantifiers based on user-provided pool annotations.
 *
 * When check is invoked, this strategy considers each
 * INST_POOL annotation on quantified formulas. For each annotation, it
 * instantiates the associated quantified formula with the Cartesian
 * product of terms currently in the pool, using efficient techniques for
 * enumerating over tuples of terms, as implemented in the term tuple
 * enumerator utilities (see quantifiers/term_tuple_enumerator.h).
 */
class InstStrategyPool : public QuantifiersModule
{
 public:
  InstStrategyPool(Env& env,
                   QuantifiersState& qs,
                   QuantifiersInferenceManager& qim,
                   QuantifiersRegistry& qr,
                   TermRegistry& tr);
  ~InstStrategyPool() {}
  /** Presolve */
  void presolve() override;
  /** Needs check. */
  bool needsCheck(Theory::Effort e) override;
  /** Reset round. */
  void reset_round(Theory::Effort e) override;
  /** Register quantified formula q */
  void registerQuantifier(Node q) override;
  /** Check ownership for q */
  void checkOwnership(Node q) override;
  /** Check.
   * Adds instantiations for all currently asserted
   * quantified formulas via calls to process(...)
   */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Identify. */
  std::string identify() const override;
  /**
   * Has standard product semantics. A pool has product semantics for a
   * quantified formula forall x : S. F if it specifies a list of sets whose
   * element types are S.
   */
  static bool hasProductSemantics(Node q, Node p);
  /**
   * Has tuple semantics. A pool has tuple semantics for a quantified formula
   * forall x : S. F if it specifies a set whose elements are (Tuple S).
   */
  static bool hasTupleSemantics(Node q, Node p);

 private:
  /** Process quantified formula with user pool, return true if we are in
   * conflict */
  bool process(Node q, Node p, uint64_t& addedLemmas);
  /** Process quantified formula with user pool with tuple semantics, return
   * true if we are in conflict */
  bool processTuple(Node q, Node p, uint64_t& addedLemmas);
  /** Map from quantified formulas to user pools */
  std::map<Node, std::vector<Node> > d_userPools;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
