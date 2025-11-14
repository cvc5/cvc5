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
 * SAT Solver creation facility.
 */

#include "prop/sat_solver_factory.h"

#include "prop/cadical/cadical.h"
#include "prop/cryptominisat.h"
#include "prop/kissat.h"
#include "prop/minisat/minisat.h"

namespace cvc5::internal {
namespace prop {

template<>
SatSolver* SatSolverFactory::createSatSolver<SatSolverFactory::CADICAL>(
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

template<>
SatSolver* SatSolverFactory::createSatSolver<SatSolverFactory::KISSAT>(
  Env& env,
  StatisticsRegistry& registry,
  ResourceManager* resmgr,
  const std::string& name)
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

template<>
SatSolver* SatSolverFactory::createSatSolver<SatSolverFactory::CRYPTO_MINISAT>(
  Env& env,
  StatisticsRegistry& registry,
  ResourceManager* resmgr,
  const std::string& name)
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

template<>
CDCLTSatSolver* SatSolverFactory::createCDCLTSatSolver<SatSolverFactory::MINISAT>(
  Env& env,
  StatisticsRegistry& registry,
  ResourceManager* resmgr,
  TheoryProxy* theory_proxy,
  const std::string& name)
{
  MinisatSatSolver* res = new MinisatSatSolver(env, registry);
  res->initialize(theory_proxy);
  return res;
}

template<>
CDCLTSatSolver* SatSolverFactory::createCDCLTSatSolver<SatSolverFactory::CADICAL>(
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
