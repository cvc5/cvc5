/*********************                                                        */
/*! \file sat_solver_factory.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Aina Niemetz, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SAT Solver creation facility.
 **
 ** SAT Solver.
 **/

#include "prop/sat_solver_factory.h"

#include "prop/bvminisat/bvminisat.h"
#include "prop/cadical.h"
#include "prop/cryptominisat.h"
#include "prop/kissat.h"
#include "prop/minisat/minisat.h"

namespace CVC4 {
namespace prop {

BVSatSolverInterface* SatSolverFactory::createMinisat(
    context::Context* mainSatContext,
    StatisticsRegistry* registry,
    const std::string& name)
{
  return new BVMinisatSatSolver(registry, mainSatContext, name);
}

DPLLSatSolverInterface* SatSolverFactory::createDPLLMinisat(
    StatisticsRegistry* registry)
{
  return new MinisatSatSolver(registry);
}

SatSolver* SatSolverFactory::createCryptoMinisat(StatisticsRegistry* registry,
                                                 const std::string& name)
{
#ifdef CVC4_USE_CRYPTOMINISAT
  CryptoMinisatSolver* res = new CryptoMinisatSolver(registry, name);
  res->init();
  return res;
#else
  Unreachable() << "CVC4 was not compiled with Cryptominisat support.";
#endif
}

SatSolver* SatSolverFactory::createCadical(StatisticsRegistry* registry,
                                           const std::string& name)
{
#ifdef CVC4_USE_CADICAL
  CadicalSolver* res = new CadicalSolver(registry, name);
  res->init();
  return res;
#else
  Unreachable() << "CVC4 was not compiled with CaDiCaL support.";
#endif
}

SatSolver* SatSolverFactory::createKissat(StatisticsRegistry* registry,
                                          const std::string& name)
{
#ifdef CVC4_USE_KISSAT
  KissatSolver* res = new KissatSolver(registry, name);
  res->init();
  return res;
#else
  Unreachable() << "CVC4 was not compiled with Kissat support.";
#endif
}

}  // namespace prop
}  // namespace CVC4
