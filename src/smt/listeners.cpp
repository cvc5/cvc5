/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements listener classes for SMT engine.
 */

#include "smt/listeners.h"

#include "smt/solver_engine.h"

namespace cvc5::internal {
namespace smt {

ResourceOutListener::ResourceOutListener(SolverEngine& slv) : d_slv(slv) {}

void ResourceOutListener::notify()
{
  d_slv.interrupt();
}

}  // namespace smt
}  // namespace cvc5::internal
