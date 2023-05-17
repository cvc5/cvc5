/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Instantiation engine strategy base class.
 */

#include "theory/quantifiers/ematching/inst_strategy.h"

#include "smt/env.h"
#include "theory/quantifiers/quantifiers_state.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstStrategy::InstStrategy(Env& env,
                           inst::TriggerDatabase& td,
                           QuantifiersState& qs,
                           QuantifiersInferenceManager& qim,
                           QuantifiersRegistry& qr,
                           TermRegistry& tr)
    : EnvObj(env), d_td(td), d_qstate(qs), d_qim(qim), d_qreg(qr), d_treg(tr)
{
}
InstStrategy::~InstStrategy() {}
void InstStrategy::presolve() {}
std::string InstStrategy::identify() const { return std::string("Unknown"); }

options::UserPatMode InstStrategy::getInstUserPatMode() const
{
  if (options().quantifiers.userPatternsQuant
      == options::UserPatMode::INTERLEAVE)
  {
    return d_qstate.getInstRounds() % 2 == 0 ? options::UserPatMode::USE
                                             : options::UserPatMode::RESORT;
  }
  return options().quantifiers.userPatternsQuant;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
