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

#include "prop/cadical.h"
#include "prop/cryptominisat.h"
#include "prop/kissat.h"
#include "prop/minisat/minisat.h"

namespace cvc5::internal {
namespace prop {

CDCLTSatSolver* SatSolverFactory::createCDCLTMinisat(
    Env& env, StatisticsRegistry& registry)
{
  return new MinisatSatSolver(env, registry);
}

SatSolver* SatSolverFactory::createCryptoMinisat(StatisticsRegistry& registry,
                                                 ResourceManager* resmgr,
                                                 const std::string& name)
{
#ifdef CVC5_USE_CRYPTOMINISAT
  CryptoMinisatSolver* res = new CryptoMinisatSolver(registry, name);
  res->init();
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

CDCLTSatSolver* SatSolverFactory::createCadical(Env& env,
                                                StatisticsRegistry& registry,
                                                ResourceManager* resmgr,
                                                const std::string& name)
{
  CadicalSolver* res = new CadicalSolver(env, registry, name);
  res->init();
  res->setResourceLimit(resmgr);
  return res;
}

CDCLTSatSolver* SatSolverFactory::createCadicalCDCLT(
    Env& env,
    StatisticsRegistry& registry,
    ResourceManager* resmgr,
    const std::string& name)
{
  CadicalSolver* res = new CadicalSolver(env, registry, name);
  res->setResourceLimit(resmgr);
  return res;
}

SatSolver* SatSolverFactory::createKissat(StatisticsRegistry& registry,
                                          const std::string& name)
{
#ifdef CVC5_USE_KISSAT
  KissatSolver* res = new KissatSolver(registry, name);
  res->init();
  return res;
#else
  Unreachable() << "cvc5 was not compiled with Kissat support.";
  return nullptr;
#endif
}

}  // namespace prop
}  // namespace cvc5::internal
