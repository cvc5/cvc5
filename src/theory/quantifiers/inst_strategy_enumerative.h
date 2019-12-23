/*********************                                                        */
/*! \file inst_strategy_enumerative.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumerative instantiation
 **/

#include "cvc4_private.h"

#ifndef CVC4__INST_STRATEGY_ENUMERATIVE_H
#define CVC4__INST_STRATEGY_ENUMERATIVE_H

#include "context/context.h"
#include "context/context_mm.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/relevant_domain.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Enumerative instantiation
 *
 * This class implements enumerative instantiation described
 * in Reynolds et al., "Revisiting Enumerative Instantiation".
 *
 * It is an instance of QuantifiersModule, whose main
 * task is to make calls to QuantifiersEngine during
 * calls to QuantifiersModule::check(...).
 *
 * This class adds instantiations based on enumerating
 * well-typed terms that occur in the current context
 * based on a heuristically determined ordering on
 * tuples of terms. This ordering incorporates
 * reasoning about the relevant domain of quantified
 * formulas (see theory/quantifiers/relevant_domain.h).
 * We consider only ground terms that occur in the
 * context due to Theorem 1 of "Revisiting Enumerative
 * Instantiation". Notice this theorem holds only for theories
 * with compactness. For theories such as arithmetic,
 * this class may introduce "default" terms that are
 * used in instantiations, say 0 for arithmetic, even
 * when the term 0 does not occur in the context.
 *
 * This strategy is not enabled by default, and
 * is enabled by the option:
 *   --full-saturate-quant
 *
 * It is generally called with lower priority than
 * other instantiation strategies, although this
 * option interleaves it with other strategies
 * during quantifier effort level QEFFORT_STANDARD:
 *   --fs-interleave
 */
class InstStrategyEnum : public QuantifiersModule
{
 public:
  InstStrategyEnum(QuantifiersEngine* qe, RelevantDomain* rd);
  ~InstStrategyEnum() {}
  /** Needs check. */
  bool needsCheck(Theory::Effort e) override;
  /** Reset round. */
  void reset_round(Theory::Effort e) override;
  /** Check.
   * Adds instantiations for all currently asserted
   * quantified formulas via calls to process(...)
   */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Identify. */
  std::string identify() const override
  {
    return std::string("InstStrategyEnum");
  }

 private:
  /** Pointer to the relevant domain utility of quantifiers engine */
  RelevantDomain* d_rd;
  /** process quantified formula
   *
   * q is the quantified formula we are constructing instances for.
   * fullEffort is whether we are called at full effort.
   *
   * If this function returns true, then one instantiation
   * (determined by an enumeration) was added via a successful
   * call to QuantifiersEngine::addInstantiation(...).
   *
   * If fullEffort is true, then we may introduce a "default"
   * well-typed term *not* occurring in the current context.
   * This handles corner cases where there are no well-typed
   * ground terms in the current context to instantiate with.
   *
   * The flag isRd indicates whether we are trying relevant domain
   * instantiations. If this flag is false, we are trying arbitrary ground
   * term instantiations.
   */
  bool process(Node q, bool fullEffort, bool isRd);
}; /* class InstStrategyEnum */

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif
