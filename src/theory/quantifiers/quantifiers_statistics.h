/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Quantifiers statistics class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_STATISTICS_H
#define CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_STATISTICS_H

#include "util/statistics_registry.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Statistics class for quantifiers, which contains all statistics that need
 * to be tracked globally within the quantifiers theory.
 */
class QuantifiersStatistics
{
 public:
  QuantifiersStatistics(StatisticsRegistry& sr);
  TimerStat d_time;
  TimerStat d_cbqi_time;
  TimerStat d_ematching_time;
  IntStat d_num_quant;
  IntStat d_instantiation_rounds;
  IntStat d_instantiation_rounds_lc;
  IntStat d_triggers;
  IntStat d_simple_triggers;
  IntStat d_multi_triggers;
  IntStat d_red_alpha_equiv;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_STATISTICS_H */
