/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of quantifiers statistics class.
 */

#include "theory/quantifiers/quantifiers_statistics.h"

#include "smt/smt_statistics_registry.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

QuantifiersStatistics::QuantifiersStatistics()
    : d_time(smtStatisticsRegistry().registerTimer(
        "theory::QuantifiersEngine::time")),
      d_qcf_time(smtStatisticsRegistry().registerTimer(
          "theory::QuantifiersEngine::time_qcf")),
      d_ematching_time(smtStatisticsRegistry().registerTimer(
          "theory::QuantifiersEngine::time_ematching")),
      d_num_quant(smtStatisticsRegistry().registerInt(
          "QuantifiersEngine::Num_Quantifiers")),
      d_instantiation_rounds(smtStatisticsRegistry().registerInt(
          "QuantifiersEngine::Rounds_Instantiation_Full")),
      d_instantiation_rounds_lc(smtStatisticsRegistry().registerInt(
          "QuantifiersEngine::Rounds_Instantiation_Last_Call")),
      d_triggers(
          smtStatisticsRegistry().registerInt("QuantifiersEngine::Triggers")),
      d_simple_triggers(smtStatisticsRegistry().registerInt(
          "QuantifiersEngine::Triggers_Simple")),
      d_multi_triggers(smtStatisticsRegistry().registerInt(
          "QuantifiersEngine::Triggers_Multi")),
      d_red_alpha_equiv(smtStatisticsRegistry().registerInt(
          "QuantifiersEngine::Reductions_Alpha_Equivalence"))
{
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
