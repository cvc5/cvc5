/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for management of equality engines.
 */

#include "theory/ee_manager.h"

#include "theory/theory_model.h"

namespace cvc5 {
namespace theory {

EqEngineManager::EqEngineManager(TheoryEngine& te, SharedSolver& shs)
    : d_te(te), d_sharedSolver(shs)
{
}

const EeTheoryInfo* EqEngineManager::getEeTheoryInfo(TheoryId tid) const
{
  std::map<TheoryId, EeTheoryInfo>::const_iterator it = d_einfo.find(tid);
  if (it != d_einfo.end())
  {
    return &it->second;
  }
  return nullptr;
}

eq::EqualityEngine* EqEngineManager::allocateEqualityEngine(EeSetupInfo& esi,
                                                            context::Context* c)
{
  if (esi.d_notify != nullptr)
  {
    return new eq::EqualityEngine(
        *esi.d_notify, c, esi.d_name, esi.d_constantsAreTriggers);
  }
  // the theory doesn't care about explicit notifications
  return new eq::EqualityEngine(c, esi.d_name, esi.d_constantsAreTriggers);
}

}  // namespace theory
}  // namespace cvc5
