/*********************                                                        */
/*! \file sat_solver_factory.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors:
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** SAT Solver creation facility
 **/

#pragma once

#include "cvc4_public.h"

#include "prop/sat_solver.h"

namespace CVC4 {
namespace prop {

class SatSolverFactory {
public:
  static BVSatSolverInterface* createMinisat();
  static DPLLSatSolverInterface* createDPLLMinisat();
};

}
}



