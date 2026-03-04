/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SAT Solver creation facility.
 */

#include "prop/sat_solver_factory.h"

#include "prop/cadical/cadical.h"
#include "prop/cryptominisat.h"
#include "prop/kissat.h"
#include "prop/minisat/minisat.h"

namespace cvc5::internal {
namespace prop {

SatSolverFactory::Factory SatSolverFactory::getFactory(
    const options::BvSatSolverMode mode)
{
  switch (mode)
  {
    case options::BvSatSolverMode::CADICAL:
      return createSatSolver<options::BvSatSolverMode::CADICAL>;
    case options::BvSatSolverMode::KISSAT:
      return createSatSolver<options::BvSatSolverMode::KISSAT>;
    case options::BvSatSolverMode::CRYPTOMINISAT:
      return createSatSolver<options::BvSatSolverMode::CRYPTOMINISAT>;
    default:
      Unreachable();
      return nullptr;
  }
}

SatSolverFactory::CDCLTFactory SatSolverFactory::getFactory(
    const options::SatSolverMode mode)
{
  using options::SatSolverMode;
  switch (mode)
  {
    case SatSolverMode::CADICAL:
      return createCDCLTSatSolver<SatSolverMode::CADICAL>;
    case SatSolverMode::MINISAT:
      return createCDCLTSatSolver<SatSolverMode::MINISAT>;
    default:
      Unreachable();
      return nullptr;
  }
}

template <>
SatSolver* SatSolverFactory::createSatSolver<options::BvSatSolverMode::CADICAL>(
    Env& env,
    StatisticsRegistry& registry,
    ResourceManager* resmgr,
    const std::string& name)
{
  CadicalSolver* res = new CadicalSolver(env, registry, name);
  res->initialize();
  res->setResourceLimit(resmgr);
  return res;
}

template <>
SatSolver* SatSolverFactory::createSatSolver<options::BvSatSolverMode::KISSAT>(
    CVC5_UNUSED Env& env,
    CVC5_UNUSED StatisticsRegistry& registry,
    CVC5_UNUSED ResourceManager* resmgr,
    CVC5_UNUSED const std::string& name)
{
#ifdef CVC5_USE_KISSAT
  KissatSolver* res = new KissatSolver(registry, name);
  res->initialize();
  return res;
#else
  Unreachable() << "cvc5 was not compiled with Kissat support.";
  return nullptr;
#endif
}

template <>
SatSolver* SatSolverFactory::createSatSolver<options::BvSatSolverMode::CRYPTOMINISAT>(
    CVC5_UNUSED Env& env,
    CVC5_UNUSED StatisticsRegistry& registry,
    CVC5_UNUSED ResourceManager* resmgr,
    CVC5_UNUSED const std::string& name)
{
#ifdef CVC5_USE_CRYPTOMINISAT
  CryptoMinisatSolver* res = new CryptoMinisatSolver(registry, name);
  res->initialize();
  if (resmgr->limitOn())
  {
    res->setTimeLimit(resmgr);
  }
  return res;
#else
  Unreachable() << "cvc5 was not compiled with Cryptominisat support.";
  return nullptr;
#endif
}

template <>
CDCLTSatSolver*
SatSolverFactory::createCDCLTSatSolver<options::SatSolverMode::MINISAT>(
    Env& env,
    StatisticsRegistry& registry,
    CVC5_UNUSED ResourceManager* resmgr,
    TheoryProxy* theory_proxy,
    CVC5_UNUSED const std::string& name)
{
  MinisatSatSolver* res = new MinisatSatSolver(env, registry);
  res->initialize(theory_proxy);
  return res;
}

template <>
CDCLTSatSolver*
SatSolverFactory::createCDCLTSatSolver<options::SatSolverMode::CADICAL>(
    Env& env,
    StatisticsRegistry& registry,
    ResourceManager* resmgr,
    TheoryProxy* theory_proxy,
    const std::string& name)
{
  CadicalSolver* res = new CadicalSolver(env, registry, name);
  res->setResourceLimit(resmgr);
  res->initialize(theory_proxy);
  return res;
}

}  // namespace prop
}  // namespace cvc5::internal
