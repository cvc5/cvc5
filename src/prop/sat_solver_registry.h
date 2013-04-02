/*********************                                                        */
/*! \file sat_solver_registry.h
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

#pragma once

#include "cvc4_private.h"

#include <map>
#include <string>
#include <cxxabi.h>
#include "prop/sat_solver.h"
#include "prop/sat_solver_factory.h"

namespace CVC4 {
namespace prop {

/**
 * Interface for SAT solver constructors. Solvers should declare an instantiation of the
 * SatSolverConstructor interface below.
 */
class SatSolverConstructorInterface {
public:
  virtual ~SatSolverConstructorInterface() {}
  virtual SatSolver* construct() = 0;
};

/**
 * Registry containing all the registered SAT solvers.
 */
class SatSolverRegistry {

  typedef std::map<std::string, SatSolverConstructorInterface*> registry_type;

  /** Map from ids to solver constructors */
  registry_type d_solvers;

  /** Nobody can create the registry, there can be only one! */
  SatSolverRegistry() {}

  /**
   * Register a SAT solver with the registry. The Constructor type should be a subclass
   * of the SatSolverConstructor.
   */
  template <typename Constructor>
  size_t registerSolver(const char* id) {
    int status;
    char* demangled = abi::__cxa_demangle(id, 0, 0, &status);
    d_solvers[demangled] = new Constructor();
    free(demangled);
    return d_solvers.size();
  }

  /** Get the instance of the registry */
  static SatSolverRegistry* getInstance();

public:

  /** Destructor */
  ~SatSolverRegistry();

  /**
   * Returns the constructor for the given SAT solver.
   */
  static SatSolverConstructorInterface* getConstructor(std::string id);

  /** Get the ids of the available solvers */
  static void getSolverIds(std::vector<std::string>& solvers);

  /** The Constructors are friends, since they need to register */
  template<typename Solver>
  friend class SatSolverConstructor;

};

/**
 * Declare an instance of this class with the SAT solver in order to put it in the registry.
 */
template<typename Solver>
class SatSolverConstructor : public SatSolverConstructorInterface {

  /** Static solver id we use for initialization */
  static const size_t s_solverId;

public:

  /** Constructs the solver */
  SatSolver* construct() {
    return new Solver();
  }

};

template<typename Solver>
const size_t SatSolverConstructor<Solver>::s_solverId = SatSolverRegistry::getInstance()->registerSolver<SatSolverConstructor>(typeid(Solver).name());

}
}

