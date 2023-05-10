/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of quantifier module.
 */

#include "theory/quantifiers/quant_module.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

QuantifiersModule::QuantifiersModule(
    Env& env,
    quantifiers::QuantifiersState& qs,
    quantifiers::QuantifiersInferenceManager& qim,
    quantifiers::QuantifiersRegistry& qr,
    quantifiers::TermRegistry& tr)
    : EnvObj(env), d_qstate(qs), d_qim(qim), d_qreg(qr), d_treg(tr)
{
}

QuantifiersModule::QEffort QuantifiersModule::needsModel(Theory::Effort e)
{
  return QEFFORT_NONE;
}

eq::EqualityEngine* QuantifiersModule::getEqualityEngine() const
{
  return d_qstate.getEqualityEngine();
}

bool QuantifiersModule::areEqual(TNode n1, TNode n2) const
{
  return d_qstate.areEqual(n1, n2);
}

bool QuantifiersModule::areDisequal(TNode n1, TNode n2) const
{
  return d_qstate.areDisequal(n1, n2);
}

TNode QuantifiersModule::getRepresentative(TNode n) const
{
  return d_qstate.getRepresentative(n);
}

quantifiers::TermDb* QuantifiersModule::getTermDatabase() const
{
  return d_treg.getTermDatabase();
}

quantifiers::QuantifiersState& QuantifiersModule::getState()
{
  return d_qstate;
}

quantifiers::QuantifiersInferenceManager&
QuantifiersModule::getInferenceManager()
{
  return d_qim;
}

quantifiers::QuantifiersRegistry& QuantifiersModule::getQuantifiersRegistry()
{
  return d_qreg;
}

quantifiers::TermRegistry& QuantifiersModule::getTermRegistry()
{
  return d_treg;
}

}  // namespace theory
}  // namespace cvc5::internal
