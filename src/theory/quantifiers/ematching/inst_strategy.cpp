/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Instantiation engine strategy base class.
 */

#include "theory/quantifiers/ematching/inst_strategy.h"

#include "theory/quantifiers/quantifiers_state.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

InstStrategy::InstStrategy(inst::TriggerDatabase& td,
                           QuantifiersState& qs,
                           QuantifiersInferenceManager& qim,
                           QuantifiersRegistry& qr,
                           TermRegistry& tr)
    : d_td(td), d_qstate(qs), d_qim(qim), d_qreg(qr), d_treg(tr)
{
}
InstStrategy::~InstStrategy() {}
void InstStrategy::presolve() {}
std::string InstStrategy::identify() const { return std::string("Unknown"); }

options::UserPatMode InstStrategy::getInstUserPatMode() const
{
  if (options::userPatternsQuant() == options::UserPatMode::INTERLEAVE)
  {
    return d_qstate.getInstRounds() % 2 == 0 ? options::UserPatMode::USE
                                             : options::UserPatMode::RESORT;
  }
  return options::userPatternsQuant();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
