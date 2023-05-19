/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of quantifiers statistics class.
 */

#include "theory/quantifiers/quantifiers_statistics.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

QuantifiersStatistics::QuantifiersStatistics(StatisticsRegistry& sr)
    : d_time(sr.registerTimer("theory::QuantifiersEngine::time")),
      d_cbqi_time(sr.registerTimer(
          "theory::QuantifiersEngine::time_conflict_based_inst")),
      d_ematching_time(
          sr.registerTimer("theory::QuantifiersEngine::time_ematching")),
      d_num_quant(sr.registerInt("QuantifiersEngine::Num_Quantifiers")),
      d_instantiation_rounds(
          sr.registerInt("QuantifiersEngine::Rounds_Instantiation_Full")),
      d_instantiation_rounds_lc(
          sr.registerInt("QuantifiersEngine::Rounds_Instantiation_Last_Call")),
      d_triggers(sr.registerInt("QuantifiersEngine::Triggers")),
      d_simple_triggers(sr.registerInt("QuantifiersEngine::Triggers_Simple")),
      d_multi_triggers(sr.registerInt("QuantifiersEngine::Triggers_Multi")),
      d_red_alpha_equiv(
          sr.registerInt("QuantifiersEngine::Reductions_Alpha_Equivalence"))
{
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
