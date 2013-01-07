#pragma once

#include "cvc4_private.h"

#include <map>
#include <string>
#include <cxxabi.h>

#include "mcsat/plugin/solver_plugin.h"
#include "mcsat/plugin/solver_plugin_factory.h"

namespace CVC4 {
namespace mcsat {

class ISolverPluginConstructor {
public:
  virtual ~ISolverPluginConstructor() {}
  virtual SolverPlugin* construct(ClauseDatabase& clauseDb, const SolverTrail& d_trail, SolverPluginRequest& request) = 0;
};

/**
 * Declare an template instance of this class after the solver plugin in order to put it in the registry.
 */
template<typename Solver>
class SolverPluginConstructor : public ISolverPluginConstructor {

  /** Static solver id we use for initialization */
  static const size_t s_solverId;

public:

  /** Destructor */
  ~SolverPluginConstructor() {};

  /** Constructs the solver */
  SolverPlugin* construct(ClauseDatabase& clauseDb, const SolverTrail& trail, SolverPluginRequest& request) {
    return new Solver(clauseDb, trail, request);
  }

  /** The id of the solver constructor */
  static size_t getId() { return s_solverId; }
};

/**
 * Registry containing all the registered model-based theory solvers.
 */
class SolverPluginRegistry {

  typedef std::map<std::string, ISolverPluginConstructor*> registry_type;

  /** Map from ids to solver constructors */
  registry_type d_solverConstructors;

  /** Nobody can create the registry, there can be only one! */
  SolverPluginRegistry() {}

  template<typename Solver>
  friend class SolverPluginConstructor;

  /**
   * Register a solver plugin with the registry. The Constructor type should be a subclass
   * of the SolverPluginConstructor.
   */
  template <typename Constructor>
  size_t registerSolver(const char* id) {
    int status;
    char* demangled = abi::__cxa_demangle(id, 0, 0, &status);
    d_solverConstructors[demangled] = new Constructor();
    free(demangled);
    return d_solverConstructors.size();
  }

  /** Get the instance of the registry */
  static SolverPluginRegistry* getInstance();

public:

  /** Destructor */
  ~SolverPluginRegistry();

  /**
   * Returns the constructor for the given SAT solver.
   */
  static ISolverPluginConstructor* getConstructor(std::string id);

  /** Returns all available plugins */
  static void getAvailablePlugins(std::vector<std::string>& plugins);

  /** The Constructors are friends, since they need to register */
  template<typename Solver>
  friend class SatSolverConstructor;

};

/** Actually register the solver */
template<typename Solver>
const size_t SolverPluginConstructor<Solver>::s_solverId = SolverPluginRegistry::getInstance()->registerSolver<SolverPluginConstructor>(typeid(Solver).name());

#define MCSAT_REGISTER_PLUGIN(PLUGIN) template class SolverPluginConstructor<PLUGIN>;

}
}
