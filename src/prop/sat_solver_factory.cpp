/*********************                                                        */
/*! \file sat_solver_factory.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors:
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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

BVSatSolverInterface* SatSolverFactory::createMinisat(context::Context* mainSatContext) {
  return new BVMinisatSatSolver(mainSatContext);
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

} /* namespace CVC4::prop */
} /* namespace CVC4 */
