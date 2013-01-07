#pragma once

#include "mcsat/plugin/solver_plugin.h"
#include "mcsat/variable/variable_table.h"
#include "mcsat/util/assigned_watch_manager.h"
#include "mcsat/rules/ackermann_rule.h"

#include "util/statistics_registry.h"

#include "context/cdlist.h"
#include "context/cdhashmap.h"
#include "context/cdinsert_hashmap.h"

namespace CVC4 {
namespace mcsat {

/** Statistics for the value selection */
struct UFPluginStats {
  /** Conflicts */
  IntStat conflicts;
  /** UF Applications */
  IntStat applications;

  UFPluginStats()
  : conflicts("mcsat::uf::conflicts", 0)
  , applications("mcsat::uf::applications", 0)
  {
    StatisticsRegistry::registerStat(&conflicts);
    StatisticsRegistry::registerStat(&applications);
  }

  ~UFPluginStats() {
    StatisticsRegistry::unregisterStat(&conflicts);
    StatisticsRegistry::unregisterStat(&applications);
  }
};

/**
 * Simple UF by filtering the model (Ackermanization)
 */
class UFPlugin : public SolverPlugin {

  UFPluginStats d_stats;

  class NewVariableNotify : public VariableDatabase::INewVariableNotify {
    UFPlugin& d_plugin;
  public:
    NewVariableNotify(UFPlugin& d_plugin);
    void newVariable(Variable var);
  } d_newVariableNotify;

  /** Called on arithmetic constraints */
  void newUninterpretedFunction(Variable f_app);

  /** Head pointer into the trail */
  context::CDO<size_t> d_trailHead;

  /** Watch manager for assigned variables */
  util::AssignedWatchManager d_assignedWatchManager;

  struct value_info {
    /** The application that was assigned */
    Variable app;
    /** The value that it is assigned to */
    TNode value;
    
    value_info() {}
    value_info(Variable app, TNode value)
    : app(app), value(value) {}
  };
  
  typedef context::CDHashMap<Node, value_info, NodeHashFunction> value_map;
  typedef context::CDInsertHashMap<Variable, Node, VariableHashFunction> evaluation_map;
  
  /** Map from evaluated applications to values (null if none yet) */
  value_map d_valueMap;

  /** Map from variables to their evluated node */
  evaluation_map d_appEvaluation;
  
  /** Mark the application children as assigned */
  void markChildrenAssigned(Variable fApp);

  /** Are all the children assigned */
  bool hasChildrenAssigned(Variable fApp) const;
  
  /** The conflicts f1 != f2 with equal args */
  std::vector< std::pair<Variable, Variable> > d_conflicts;
  
  /** Mark an application f(a1, ..., an) -> a*/
  void markAppAssigned(Variable fApp);

  /** Ackermannization */
  rules::AckermannRule d_ackermannRule;
    
public:

  UFPlugin(ClauseDatabase& clauseDb, const SolverTrail& trail, SolverPluginRequest& request);
  
  /** Perform propagation */
  void propagate(SolverTrail::PropagationToken& out);

  /** String representation of the plugin (for debug purposes mainly) */
  std::string toString() const;

  /** Notification of unset variables */
  void notifyBackjump(const std::vector<Variable>& vars);

  /** Mark phase of the GC */
  void gcMark(std::set<Variable>& varsToKeep, std::set<CRef>& clausesToKeep);

  /** Relocation phase of the GC */
  void gcRelocate(const VariableGCInfo& vReloc, const ClauseRelocationInfo& cReloc);

};

// Register the plugin
MCSAT_REGISTER_PLUGIN(UFPlugin);

}
}



