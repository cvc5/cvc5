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
#include "prop/minisat/minisat.h"
#include "prop/bvminisat/bvminisat.h"

using namespace CVC4;
using namespace prop;

BVSatSolverInterface* SatSolverFactory::createMinisat() {
  return new MinisatSatSolver();
}

DPLLSatSolverInterface* SatSolverFactory::createDPLLMinisat() {
  return new DPLLMinisatSatSolver();
}




