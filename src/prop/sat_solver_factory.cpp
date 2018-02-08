/*********************                                                        */
/*! \file sat_solver_factory.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Tim King, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SAT Solver creation facility.
 **
 ** SAT Solver.
 **/

#include "prop/sat_solver_factory.h"

// Cryptominisat header has to come first since there are name clashes for
// var_Undef, l_True, ... (static const in Cryptominisat vs. #define in Minisat)
#include "prop/cryptominisat.h"
#include "prop/minisat/minisat.h"
#include "prop/bvminisat/bvminisat.h"

namespace CVC4 {
namespace prop {

BVSatSolverInterface* SatSolverFactory::createMinisat(
    context::Context* mainSatContext,
    StatisticsRegistry* registry,
    const std::string& name)
{
  return new BVMinisatSatSolver(registry, mainSatContext, name);
}

SatSolver* SatSolverFactory::createCryptoMinisat(StatisticsRegistry* registry,
                                                 const std::string& name)
{
#ifdef CVC4_USE_CRYPTOMINISAT
  return new CryptoMinisatSolver(registry, name);
#else
  Unreachable("CVC4 was not compiled with Cryptominisat support.");
#endif
}

DPLLSatSolverInterface* SatSolverFactory::createDPLLMinisat(
    StatisticsRegistry* registry)
{
  return new MinisatSatSolver(registry);
}

}  // namespace prop
}  // namespace CVC4
