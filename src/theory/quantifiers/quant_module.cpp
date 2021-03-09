/*********************                                                        */
/*! \file quant_module.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of quantifier module
 **/

#include "theory/quantifiers/quant_module.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

QuantifiersModule::QuantifiersModule(
    quantifiers::QuantifiersState& qs,
    quantifiers::QuantifiersInferenceManager& qim,
    quantifiers::QuantifiersRegistry& qr,
    QuantifiersEngine* qe)
    : d_quantEngine(qe), d_qstate(qs), d_qim(qim), d_qreg(qr)
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

QuantifiersEngine* QuantifiersModule::getQuantifiersEngine() const
{
  return d_quantEngine;
}

quantifiers::TermDb* QuantifiersModule::getTermDatabase() const
{
  return d_quantEngine->getTermDatabase();
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

}  // namespace theory
} /* namespace CVC4 */
