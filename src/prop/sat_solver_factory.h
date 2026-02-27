/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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

#include "options/bv_options.h"
#include "options/prop_options.h"
#include "util/resource_manager.h"

#include "smt/env.h"
#include "prop/sat_solver.h"

namespace cvc5::internal {
namespace prop {

class TheoryProxy;

class SatSolverFactory
{
 public:
  using Factory = SatSolver* (*) (Env&,
                                  StatisticsRegistry&,
                                  ResourceManager*,
                                  const std::string&);

  using CDCLTFactory = CDCLTSatSolver* (*) (Env&,
                                            StatisticsRegistry&,
                                            ResourceManager*,
                                            TheoryProxy*,
                                            const std::string&);

  template <options::BvSatSolverMode T>
  static SatSolver* createSatSolver(Env& env,
                                    StatisticsRegistry& registry,
                                    ResourceManager* resmgr,
                                    const std::string& name = "");

  template <options::SatSolverMode T>
  static CDCLTSatSolver* createCDCLTSatSolver(Env& env,
                                              StatisticsRegistry& registry,
                                              ResourceManager* resmgr,
                                              TheoryProxy* theory_proxy,
                                              const std::string& name = "");

  static Factory getFactory(options::BvSatSolverMode);
  static CDCLTFactory getFactory(options::SatSolverMode);
};

template <>
SatSolver* SatSolverFactory::createSatSolver<options::BvSatSolverMode::CADICAL>(
    Env&, StatisticsRegistry&, ResourceManager*, const std::string&);

template <>
SatSolver* SatSolverFactory::createSatSolver<options::BvSatSolverMode::KISSAT>(
    Env&, StatisticsRegistry&, ResourceManager*, const std::string&);

template <>
SatSolver* SatSolverFactory::createSatSolver<options::BvSatSolverMode::CRYPTOMINISAT>(
    Env&, StatisticsRegistry&, ResourceManager*, const std::string&);

template <>
CDCLTSatSolver*
SatSolverFactory::createCDCLTSatSolver<options::SatSolverMode::MINISAT>(
    Env&,
    StatisticsRegistry&,
    ResourceManager*,
    TheoryProxy*,
    const std::string&);

template <>
CDCLTSatSolver*
SatSolverFactory::createCDCLTSatSolver<options::SatSolverMode::CADICAL>(
    Env&,
    StatisticsRegistry&,
    ResourceManager*,
    TheoryProxy*,
    const std::string&);

}  // namespace prop
}  // namespace cvc5::internal

#endif  // CVC5__PROP__SAT_SOLVER_FACTORY_H
