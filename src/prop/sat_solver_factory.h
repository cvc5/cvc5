/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SAT Solver creation facility
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__SAT_SOLVER_FACTORY_H
#define CVC5__PROP__SAT_SOLVER_FACTORY_H

#include <string>
#include <vector>

#include "context/context.h"
#include "prop/sat_solver.h"
#include "smt/env.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace prop {

class SatSolverFactory
{
 public:
  static CDCLTSatSolver* createCDCLTMinisat(Env& env,
                                            StatisticsRegistry& registry);

  static SatSolver* createCryptoMinisat(StatisticsRegistry& registry,
                                        ResourceManager* resmgr,
                                        const std::string& name = "");

  static SatSolver* createCadical(StatisticsRegistry& registry,
                                  ResourceManager* resmgr,
                                  const std::string& name = "");

  static SatSolver* createKissat(StatisticsRegistry& registry,
                                 const std::string& name = "");
}; /* class SatSolverFactory */

}  // namespace prop
}  // namespace cvc5::internal

#endif  // CVC5__PROP__SAT_SOLVER_FACTORY_H
