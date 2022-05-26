/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements listener classes for SMT engine.
 */

#include "smt/listeners.h"

#include "smt/solver_engine.h"
#include "smt/solver_engine_scope.h"

namespace cvc5::internal {
namespace smt {

ResourceOutListener::ResourceOutListener(SolverEngine& slv) : d_slv(slv) {}

void ResourceOutListener::notify()
{
  SolverEngineScope scope(&d_slv);
  d_slv.interrupt();
}

}  // namespace smt
}  // namespace cvc5::internal
