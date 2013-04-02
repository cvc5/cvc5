/*********************                                                        */
/*! \file sat_solver_registry.cpp
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This class transforms a sequence of formulas into clauses.
 **
 ** This class takes a sequence of formulas.
 ** It outputs a stream of clauses that is propositionally
 ** equi-satisfiable with the conjunction of the formulas.
 ** This stream is maintained in an online fashion.
 **
 ** Compile time registration of SAT solvers with the SAT solver factory
 **/

#include "prop/sat_solver_registry.h"
#include "sstream"

using namespace std;
using namespace CVC4;
using namespace prop;

SatSolverConstructorInterface* SatSolverRegistry::getConstructor(string id) {
  SatSolverRegistry* registry = getInstance();
  registry_type::const_iterator find = registry->d_solvers.find(id);
  if (find == registry->d_solvers.end()) {
    return NULL;
  } else {
    return find->second;
  }
}

void SatSolverRegistry::getSolverIds(std::vector<std::string>& solvers) {
  SatSolverRegistry* registry = getInstance();
  registry_type::const_iterator it = registry->d_solvers.begin();
  registry_type::const_iterator it_end = registry->d_solvers.end();
  for (; it != it_end; ++ it) {
    solvers.push_back(it->first);
  }
}

SatSolverRegistry* SatSolverRegistry::getInstance() {
  static SatSolverRegistry registry;
  return &registry;
}

SatSolverRegistry::~SatSolverRegistry() {
  registry_type::const_iterator it = d_solvers.begin();
  registry_type::const_iterator it_end = d_solvers.begin();
  for (; it != it_end; ++ it) {
    delete it->second;
  }
}
