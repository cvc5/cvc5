#pragma once

#include "mcsat/plugin/solver_plugin.h"
#include "mcsat/bcp/watch_list_manager.h"
#include "mcsat/util/var_priority_queue.h"

namespace CVC4 {
namespace mcsat {
  
/**
 * Boolean constraint propagation (BCP) engine.
 */
class BCPEngine : public SolverPlugin {

  /** Type index for the boolean type */
  size_t d_boolTypeIndex;
  
  /** Watch lists */
  WatchListManager d_watchManager;

  class NewClauseNotify : public ClauseDatabase::INewClauseNotify {
    BCPEngine& d_engine;
  public:
    NewClauseNotify(BCPEngine& d_engine);
    void newClause(CRef cref);
  };

  class NewVariableNotify : public VariableDatabase::INewVariableNotify {
    BCPEngine& d_engine;
    size_t d_bool_type_index;
  public:
    NewVariableNotify(BCPEngine& engine);
    void newVariable(Variable var);
  };

  /** Notification for new clauses */
  NewClauseNotify d_newClauseNotify;

  /** Notification for new variables */
  NewVariableNotify d_newVariableNotify;

  /** Delayed propagations (c[0] is propagated) */
  std::vector<CRef> d_delayedPropagations;

  /** New clause */
  void newClause(CRef cref);

  /** New variable */
  void newVariable(Variable var);

  /** Head pointer into the trail */
  context::CDO<size_t> d_trailHead;

  /** Values of variables */
  std::vector<bool> d_variableValues;
    
  /** How many restarts have happened */
  unsigned d_restartsCount;
  
  /** The base of the Luby sequence powers */
  double d_restartBase;

  /** The initial number of conflicts for the restart */
  unsigned d_restartInit;
  
  /** How many conflicts have happened */
  unsigned d_conflictsCount;
  
  /** How many conflicts until for a restart */
  unsigned d_conflictsLimit;

public:
  
  /** New propagation engine */
  BCPEngine(ClauseDatabase& clauseDb, const SolverTrail& trail, SolverPluginRequest& request, StatisticsRegistry* registry);
  
  /** Perform a propagation */
  void propagate(SolverTrail::PropagationToken& out);

  /** Perform a decision */
  void decide(SolverTrail::DecisionToken& out, Variable var);

  /** Notification of a new conflict */
  void notifyConflict();
  
  /** Notification of a new conflict resolution step */
  void notifyConflictResolution(CRef clause);
  
  /** Notification of unset variables */
  void notifyBackjump(const std::vector<Variable>& vars);
    
  /** Notification of restarts */
  void notifyRestart();
  
  /** Mark phase of the GC */
  void gcMark(std::set<Variable>& varsToKeep, std::set<CRef>& clausesToKeep);

  /** Relocation phase of the GC */
  void gcRelocate(const VariableGCInfo& vReloc, const ClauseRelocationInfo& cReloc);

  /** String representation */
  std::string toString() const { return "BCP Engine"; }
};

// Register the plugin
MCSAT_REGISTER_PLUGIN(BCPEngine);

}
}
