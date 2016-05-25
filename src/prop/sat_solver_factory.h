/*********************                                                        */
/*! \file sat_solver_factory.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** SAT Solver creation facility
 **/

#include "cvc4_private.h"

#pragma once

#include <string>
#include <vector>

#include "context/context.h"
#include "prop/sat_solver.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace prop {

class SatSolverFactory {
public:

  static BVSatSolverInterface* createMinisat(context::Context* mainSatContext,
                                             StatisticsRegistry* registry,
                                             const std::string& name = "");
  static DPLLSatSolverInterface* createDPLLMinisat(StatisticsRegistry* registry);
  static SatSolver* createCryptoMinisat(StatisticsRegistry* registry,
                                        const std::string& name = "");

};/* class SatSolverFactory */

}/* CVC4::prop namespace */
}/* CVC4 namespace */
