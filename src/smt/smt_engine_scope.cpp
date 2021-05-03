/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "smt/smt_engine_scope.h"

#include "base/check.h"
#include "base/configuration_private.h"
#include "base/output.h"
#include "smt/smt_engine.h"

namespace cvc5 {
namespace smt {

thread_local SmtEngine* s_smtEngine_current = NULL;

SmtEngine* currentSmtEngine() {
  Assert(s_smtEngine_current != NULL);
  return s_smtEngine_current;
}

bool smtEngineInScope() { return s_smtEngine_current != NULL; }

ProofManager* currentProofManager() {
  Assert(s_smtEngine_current != NULL);
  return s_smtEngine_current->getProofManager();
}

ResourceManager* currentResourceManager()
{
  return s_smtEngine_current->getResourceManager();
}

SmtScope::SmtScope(const SmtEngine* smt)
    : NodeManagerScope(smt->getNodeManager()),
      d_oldSmtEngine(s_smtEngine_current),
      d_optionsScope(smt ? &const_cast<SmtEngine*>(smt)->getOptions() : nullptr)
{
  Assert(smt != NULL);
  s_smtEngine_current = const_cast<SmtEngine*>(smt);
  Debug("current") << "smt scope: " << s_smtEngine_current << std::endl;
}

SmtScope::~SmtScope() {
  s_smtEngine_current = d_oldSmtEngine;
  Debug("current") << "smt scope: returning to " << s_smtEngine_current
                   << std::endl;
}

StatisticsRegistry& SmtScope::currentStatisticsRegistry()
{
  Assert(smtEngineInScope());
  return s_smtEngine_current->getStatisticsRegistry();
}

}  // namespace smt
}  // namespace cvc5
