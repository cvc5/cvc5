#pragma once

#include "cvc4_private.h"

#include "expr/node.h"
#include "expr/kind.h"

#include "context/cdo.h"
#include "context/cdlist.h"

#include "mcsat/clause/clause_db.h"
#include "mcsat/plugin/solver_plugin_notify.h"
#include "mcsat/plugin/solver_plugin_features.h"

namespace CVC4 {
namespace mcsat {

class Solver;

class SolverPluginRequest {

  /** The solver */
  Solver* d_solver;
  
public:

  /** Construct a request token for the given solver */
  SolverPluginRequest(Solver* solver)
  : d_solver(solver) {}

  /**
   * Ask for a backtrack to given level. The level must be smaller than the current decision level. The clause
   * must not be satisfied, and it should propagate at the given level. If it doesn't propagate, a non-assigned
   * literal from the clause will be selected as a decision.
   */
  void backtrack(unsigned level, CRef cRef);
  
  /**
   * Request a round of propagation from the solver.
   */
  void propagate();

  /**
   * Ask for a search restart.
   */
  void restart();

  /**
   * Bump the variable.
   */
  void bump(Variable var, unsigned amount = 1);

  /**
   * Ask for garbage collection. Garbage collection will be performed at next restart and the plugins will get notified
   * pre and post garbage collection.
   */
  void gc();

  /**
   * Are there any pending requests. Meaning we can stop, and will be called back again.
   */
  bool pending() const;

};

/**
 * Base class for model based T-solvers.
 */
class SolverPlugin : public SolverPluginNotify, public SolverPluginFeatures {

private:

  SolverPlugin() CVC4_UNUSED;
  SolverPlugin(const SolverPlugin&) CVC4_UNUSED;
  SolverPlugin& operator=(const SolverPlugin&) CVC4_UNUSED;

protected:

  /** Clause database we're using */
  ClauseDatabase& d_clauseDb;

  /** The trail that the plugin should use */
  const SolverTrail& d_trail;

  /** Channel to request something from the solver */
  SolverPluginRequest& d_request;

  /** Construct the plugin. */
  SolverPlugin(ClauseDatabase& clauseDb, const SolverTrail& trail, SolverPluginRequest& request, StatisticsRegistry* registry)
  : d_clauseDb(clauseDb)
  , d_trail(trail)
  , d_request(request)
  {}

  /** Get the SAT context associated to this Theory. */
  context::Context* getSearchContext() const {
    return d_trail.getSearchContext();
  }

public:

  /** Destructor */
  virtual ~SolverPlugin() {}

  /** String representation of the plugin (for debug purposes mainly) */
  virtual std::string toString() const = 0;

  /** Mark phase of the GC */
  virtual void gcMark(std::set<Variable>& varsToKeep, std::set<CRef>& clausesToKeep) = 0;

  /** Relocation phase of the GC */
  virtual void gcRelocate(const VariableGCInfo& vReloc, const ClauseRelocationInfo& cReloc) = 0;

}; /* class SolverPlugin */

inline std::ostream& operator << (std::ostream& out, const SolverPlugin& plugin) {
  out << plugin.toString();
  return out;
}

} /* CVC4::mcsat namespace */
} /* CVC4 namespace */

#include "mcsat/plugin/solver_plugin_registry.h"
