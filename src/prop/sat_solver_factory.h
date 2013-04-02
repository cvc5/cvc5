/*********************                                                        */
/*! \file sat_solver_factory.h
 ** \verbatim
 ** Original author: Dejan Jovanović <dejan.jovanovic@gmail.com>
 ** Major contributors: none
 ** Minor contributors (to current version): Liana Hadarean <lianahady@gmail.com>, Morgan Deters <mdeters@cs.nyu.edu>
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** SAT Solver creation facility
 **/

#pragma once

#include "cvc4_public.h"

#include <string>
#include <vector>
#include "prop/sat_solver.h"

namespace CVC4 {
namespace prop {

class SatSolverFactory {
public:

  static BVSatSolverInterface* createMinisat(context::Context* mainSatContext);
  static DPLLSatSolverInterface* createDPLLMinisat();

  static SatSolver* create(const char* id);

  /** Get the solver ids that are available */
  static void getSolverIds(std::vector<std::string>& solvers);

};

}
}



