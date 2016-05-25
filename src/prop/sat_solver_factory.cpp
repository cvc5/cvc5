/*********************                                                        */
/*! \file sat_solver_factory.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SAT Solver creation facility.
 **
 ** SAT Solver.
 **/

#include "prop/sat_solver_factory.h"

#include "prop/cryptominisat.h"
#include "prop/minisat/minisat.h"
#include "prop/bvminisat/bvminisat.h"

namespace CVC4 {
namespace prop {

BVSatSolverInterface* SatSolverFactory::createMinisat(context::Context* mainSatContext, StatisticsRegistry* registry, const std::string& name) {
  return new BVMinisatSatSolver(registry, mainSatContext, name);
}

SatSolver* SatSolverFactory::createCryptoMinisat(StatisticsRegistry* registry,
                                                   const std::string& name) {
return new CryptoMinisatSolver(registry, name);
}
  

DPLLSatSolverInterface* SatSolverFactory::createDPLLMinisat(StatisticsRegistry* registry) {
  return new MinisatSatSolver(registry);
}

} /* CVC4::prop namespace */
} /* CVC4 namespace */
