/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

#include <util/resource_manager.h>

#include <string>

#include "context/context.h"
#include "prop/sat_solver.h"
#include "smt/env.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace prop {

class TheoryProxy;

class SatSolverFactory
{
 public:
  enum SatSolverType
  {
    MINISAT,
    CADICAL,
    CRYPTOMINISAT,
    KISSAT,
  };

  template <SatSolverType T>
  static SatSolver* createSatSolver(Env& env,
                                    StatisticsRegistry& registry,
                                    ResourceManager* resmgr,
                                    const std::string& name = "");

  template <SatSolverType T>
  static CDCLTSatSolver* createCDCLTSatSolver(Env& env,
                                              StatisticsRegistry& registry,
                                              ResourceManager* resmgr,
                                              TheoryProxy* theory_proxy,
                                              const std::string& name = "");
};

template <>
SatSolver* SatSolverFactory::createSatSolver<SatSolverFactory::CADICAL>(
    Env&, StatisticsRegistry&, ResourceManager*, const std::string&);

template <>
SatSolver* SatSolverFactory::createSatSolver<SatSolverFactory::KISSAT>(
    Env&, StatisticsRegistry&, ResourceManager*, const std::string&);

template <>
SatSolver* SatSolverFactory::createSatSolver<SatSolverFactory::CRYPTOMINISAT>(
    Env&, StatisticsRegistry&, ResourceManager*, const std::string&);

template <>
CDCLTSatSolver*
SatSolverFactory::createCDCLTSatSolver<SatSolverFactory::MINISAT>(
    Env&,
    StatisticsRegistry&,
    ResourceManager*,
    TheoryProxy*,
    const std::string&);

template <>
CDCLTSatSolver*
SatSolverFactory::createCDCLTSatSolver<SatSolverFactory::CADICAL>(
    Env&,
    StatisticsRegistry&,
    ResourceManager*,
    TheoryProxy*,
    const std::string&);

}  // namespace prop
}  // namespace cvc5::internal

#endif  // CVC5__PROP__SAT_SOLVER_FACTORY_H
