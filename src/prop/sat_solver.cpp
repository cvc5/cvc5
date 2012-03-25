/*********************                                                        */
/*! \file sat.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: dejan, taking, mdeters, lianah
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "prop/prop_engine.h"
#include "prop/sat_solver.h"
#include "context/context.h"
#include "theory/theory_engine.h"
#include "expr/expr_stream.h"
#include "prop/theory_proxy.h"

#include "prop/minisat/minisat.h"
#include "prop/bvminisat/bvminisat.h"

using namespace std; 

namespace CVC4 {
namespace prop {

string SatLiteral::toString() {
  ostringstream os;
  os << (isNegated()? "~" : "") << getSatVariable() << " ";
  return os.str(); 
}

BVSatSolverInterface* SatSolverFactory::createMinisat() {
  return new MinisatSatSolver(); 
}

DPLLSatSolverInterface* SatSolverFactory::createDPLLMinisat(){
  return new DPLLMinisatSatSolver(); 
} 


}/* CVC4::prop namespace */
}/* CVC4 namespace */
