/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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

#include "smt/solver_engine_scope.h"

#include "base/check.h"
#include "base/configuration_private.h"
#include "base/output.h"
#include "smt/solver_engine.h"

namespace cvc5::internal {
namespace smt {

thread_local SolverEngine* s_slvEngine_current = nullptr;

ResourceManager* currentResourceManager()
{
  return s_slvEngine_current->getResourceManager();
}

SolverEngineScope::SolverEngineScope(const SolverEngine* smt)
    : d_oldSlvEngine(s_slvEngine_current),
      d_optionsScope(smt ? &const_cast<SolverEngine*>(smt)->getOptions()
                         : nullptr)
{
  Assert(smt != nullptr);
  s_slvEngine_current = const_cast<SolverEngine*>(smt);
  Trace("current") << "smt scope: " << s_slvEngine_current << std::endl;
}

SolverEngineScope::~SolverEngineScope()
{
  s_slvEngine_current = d_oldSlvEngine;
  Trace("current") << "smt scope: returning to " << s_slvEngine_current
                   << std::endl;
}

StatisticsRegistry& SolverEngineScope::currentStatisticsRegistry()
{
  Assert(s_slvEngine_current != nullptr);
  return s_slvEngine_current->getStatisticsRegistry();
}

}  // namespace smt
}  // namespace cvc5::internal
