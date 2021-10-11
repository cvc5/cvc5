/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of OutputManager functions.
 */

#include "smt/output_manager.h"

#include "options/base_options.h"
#include "smt/solver_engine.h"

namespace cvc5 {

OutputManager::OutputManager(SolverEngine* slv) : d_slv(slv) {}

const Printer& OutputManager::getPrinter() const { return d_slv->getPrinter(); }

std::ostream& OutputManager::getDumpOut() const
{
  return *d_slv->getOptions().base.out;
}

}  // namespace cvc5
