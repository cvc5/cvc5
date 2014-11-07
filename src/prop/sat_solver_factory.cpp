/*********************                                                        */
/*! \file sat_solver_factory.cpp
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Tim King
 ** Minor contributors (to current version): Morgan Deters, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SAT Solver creation facility.
 **
 ** SAT Solver.
 **/

#include "prop/sat_solver_factory.h"
#include "prop/sat_solver_registry.h"
#include "prop/minisat/minisat.h"
#include "prop/bvminisat/bvminisat.h"

namespace CVC4 {
namespace prop {

template class SatSolverConstructor<MinisatSatSolver>;
template class SatSolverConstructor<BVMinisatSatSolver>;

BVSatSolverInterface* SatSolverFactory::createMinisat(context::Context* mainSatContext, const std::string& name) {
  return new BVMinisatSatSolver(mainSatContext, name);
}

DPLLSatSolverInterface* SatSolverFactory::createDPLLMinisat() {
  return new MinisatSatSolver();
}

SatSolver* SatSolverFactory::create(const char* name) {
  SatSolverConstructorInterface* constructor = SatSolverRegistry::getConstructor(name);
  if (constructor) {
    return constructor->construct();
  } else {
    return NULL;
  }
}

void SatSolverFactory::getSolverIds(std::vector<std::string>& solvers) {
  SatSolverRegistry::getSolverIds(solvers);
}

} /* CVC4::prop namespace */
} /* CVC4 namespace */
