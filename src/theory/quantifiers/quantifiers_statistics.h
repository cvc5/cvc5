/*********************                                                        */
/*! \file quantifiers_statistics.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Quantifiers statistics class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_STATISTICS_H
#define CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_STATISTICS_H

#include "util/statistics_registry.h"
#include "util/stats_timer.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * Statistics class for quantifiers, which contains all statistics that need
 * to be tracked globally within the quantifiers theory.
 */
class QuantifiersStatistics
{
 public:
  QuantifiersStatistics();
  ~QuantifiersStatistics();
  TimerStat d_time;
  TimerStat d_qcf_time;
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
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_STATISTICS_H */
