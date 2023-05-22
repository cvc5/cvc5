/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * dynamic quantifiers splitting
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANT_SPLIT_H
#define CVC5__THEORY__QUANT_SPLIT_H

#include "context/cdo.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

/** Quantifiers dynamic splitting
 *
 * This module identifies quantified formulas that should be "split", e.g.
 * based on datatype constructor case splitting.
 *
 * An example of a quantified formula that we may split is the following. Let:
 *   optionPair := mkPair( U, U ) | none
 * where U is an uninterpreted sort. The quantified formula:
 *   forall x : optionPair. P( x )
 * may be "split" via the lemma:
 *   forall x : optionPair. P( x ) <=>
 *   ( forall xy : U. P( mkPair( x, y ) ) OR P( none ) )
 *
 * Notice that such splitting may lead to exponential behavior, say if we
 * quantify over 32 variables of type optionPair above gives 2^32 disjuncts.
 * This class is used to compute this splitting dynamically, by splitting
 * one variable per quantified formula at a time.
 */
class QuantDSplit : public QuantifiersModule {
  typedef context::CDHashSet<Node> NodeSet;

 public:
  QuantDSplit(Env& env,
              QuantifiersState& qs,
              QuantifiersInferenceManager& qim,
              QuantifiersRegistry& qr,
              TermRegistry& tr);
  /** determine whether this quantified formula will be reduced */
  void checkOwnership(Node q) override;
  /* whether this module needs to check this round */
  bool needsCheck(Theory::Effort e) override;
  /* Call during quantifier engine's check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** check complete for */
  bool checkCompleteFor(Node q) override;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const override { return "QuantDSplit"; }

 private:
  /** list of relevant quantifiers asserted in the current context */
  std::map<Node, int> d_quant_to_reduce;
  /** whether we have instantiated quantified formulas */
  NodeSet d_added_split;
};

}
}
}  // namespace cvc5::internal

#endif
