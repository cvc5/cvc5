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

#include "prop/cryptominisat.h"
#include "prop/riss.h"
#include "prop/glucose.h"
#include "prop/sat_solver_factory.h"
#include "prop/minisat/minisat.h"
#include "prop/bvminisat/bvminisat.h"


namespace CVC4 {
namespace prop {
  
  BVSatSolverInterface* SatSolverFactory::createMinisat(context::Context* mainSatContext,
							const std::string& name) {
    return new BVMinisatSatSolver(mainSatContext, name);
  }
  
  SatSolver* SatSolverFactory::createCryptoMinisat(const std::string& name) {
    return new CryptoMinisatSolver(name);
  }
  
  SatSolver* SatSolverFactory::createRiss(const std::string& name) {
   return new RissSolver(name);
  }
  
  SatSolver* SatSolverFactory::createGlucose(const std::string& name) {
    return new GlucoseSolver(name);
  }
  
  
  DPLLSatSolverInterface* SatSolverFactory::createDPLLMinisat() {
    return new MinisatSatSolver();
  }
  
} /* CVC4::prop namespace */
} /* CVC4 namespace */
