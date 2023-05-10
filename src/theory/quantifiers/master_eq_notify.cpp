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
 * Notification class for the master equality engine
 */

#include "theory/quantifiers/master_eq_notify.h"

#include "theory/quantifiers_engine.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

MasterNotifyClass::MasterNotifyClass(QuantifiersEngine* qe) : d_quantEngine(qe) {}

void MasterNotifyClass::eqNotifyNewClass(TNode t)
{
  d_quantEngine->eqNotifyNewClass(t);
}


}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
