/*********************                                                        */
/*! \file smt_engine_scope.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "smt/smt_engine_scope.h"

#include "base/check.h"
#include "base/configuration_private.h"
#include "base/output.h"
#include "proof/proof.h"
#include "smt/smt_engine.h"

namespace CVC4 {
namespace smt {

thread_local SmtEngine* s_smtEngine_current = NULL;

SmtEngine* currentSmtEngine() {
  Assert(s_smtEngine_current != NULL);
  return s_smtEngine_current;
}

bool smtEngineInScope() { return s_smtEngine_current != NULL; }

ProofManager* currentProofManager() {
#if IS_PROOFS_BUILD
  Assert(s_smtEngine_current != NULL);
  return s_smtEngine_current->getProofManager();
#else  /* IS_PROOFS_BUILD */
  InternalError()
      << "proofs/unsat cores are not on, but ProofManager requested";
  return NULL;
#endif /* IS_PROOFS_BUILD */
}

ResourceManager* currentResourceManager()
{
  return s_smtEngine_current->getResourceManager();
}

SmtScope::SmtScope(const SmtEngine* smt)
    : NodeManagerScope(smt->d_nodeManager),
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

StatisticsRegistry* SmtScope::currentStatisticsRegistry() {
  Assert(smtEngineInScope());
  return s_smtEngine_current->getStatisticsRegistry();
}

}/* CVC4::smt namespace */
}/* CVC4 namespace */
