/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SAT Solver creation facility.
 */

#include "prop/sat_solver_factory.h"

#include "prop/bvminisat/bvminisat.h"
#include "prop/cadical.h"
#include "prop/cryptominisat.h"
#include "prop/kissat.h"
#include "prop/minisat/minisat.h"

namespace cvc5 {
namespace prop {

BVSatSolverInterface* SatSolverFactory::createMinisat(
    context::Context* mainSatContext,
    StatisticsRegistry& registry,
    const std::string& name)
{
  return new BVMinisatSatSolver(registry, mainSatContext, name);
}

MinisatSatSolver* SatSolverFactory::createCDCLTMinisat(
    StatisticsRegistry& registry)
{
  return new MinisatSatSolver(registry);
}

SatSolver* SatSolverFactory::createCryptoMinisat(StatisticsRegistry& registry,
                                                 const std::string& name)
{
#ifdef CVC5_USE_CRYPTOMINISAT
  CryptoMinisatSolver* res = new CryptoMinisatSolver(registry, name);
  res->init();
  return res;
#else
  Unreachable() << "cvc5 was not compiled with Cryptominisat support.";
#endif
}

SatSolver* SatSolverFactory::createCadical(StatisticsRegistry& registry,
                                           const std::string& name)
{
#ifdef CVC5_USE_CADICAL
  CadicalSolver* res = new CadicalSolver(registry, name);
  res->init();
  return res;
#else
  Unreachable() << "cvc5 was not compiled with CaDiCaL support.";
#endif
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
#endif
}

}  // namespace prop
}  // namespace cvc5
