#pragma once

#include "mcsat/plugin/solver_plugin.h"
#include "mcsat/variable/variable_table.h"

#include "mcsat/fm/bounds_model.h"

#include "mcsat/util/assigned_watch_manager.h"

#include "mcsat/rules/fourier_motzkin_rule.h"
#include "mcsat/rules/int_split_rule.h"

namespace CVC4 {
namespace mcsat {

/** Statistics for the value selection */
struct FMPluginStats {
  /** Number of decisions */
  IntStat decisions;
  /** Number of fixed decisions */
  IntStat decisions_f;
  /** Conflicts */
  IntStat conflicts;
  /** Number of propagations (semantic, x -> 1 => x > 0) */
  IntStat propagationS;
  /** Number of propagations (deductive, x > 1 => x > 0) */
  IntStat propagationD;
  /** Number of [.... selections */

  StatisticsRegistry* d_registry;

  FMPluginStats (StatisticsRegistry* registry)
  : decisions("mcsat::fm::decisions", 0)
  , decisions_f("mcsat::fm::decisions_f", 0)
  , conflicts("mcsat::fm::conflicts", 0)
  , propagationS("mcsat::fm::propagations_s", 0)
  , propagationD("mcsat::fm::propagations_d", 0)
  , d_registry(registry)
  {
    d_registry->registerStat(&decisions);
    d_registry->registerStat(&decisions_f);
    d_registry->registerStat(&conflicts);
    d_registry->registerStat(&propagationS);
    d_registry->registerStat(&propagationD);
  }

  ~FMPluginStats () {
    d_registry->unregisterStat(&decisions);
    d_registry->unregisterStat(&decisions_f);
    d_registry->unregisterStat(&conflicts);
    d_registry->unregisterStat(&propagationS);
    d_registry->unregisterStat(&propagationD);
  }
};

/**
 * Fourier-Motzkin elimination plugin.
 */
class FMPlugin : public SolverPlugin {

  FMPluginStats d_stats;

  class NewVariableNotify : public VariableDatabase::INewVariableNotify {
    FMPlugin& d_plugin;
  public:
    NewVariableNotify(FMPlugin& d_plugin);
    void newVariable(Variable var);
  } d_newVariableNotify;

  /** Integer type index */
  size_t d_intTypeIndex;

  /** Real type index */
  size_t d_realTypeIndex;

  /** Bool type index */
  size_t d_boolTypeIndex;
  
  /** The learned clauses */
  std::vector<CRef> d_lemmasLearnt;

  /** Called on arithmetic constraints */
  void newConstraint(Variable constraint);

  class unit_info {
    
    /** Last unit variable */
    Variable var;
    /** Are we unit */
    bool unit;
 
  public:
    
    unit_info(): unit(false) {}
    
    bool isUnit() const { 
      return unit && !var.isNull();
    }
    
    void setUnit(Variable v) {
      var = v;
      unit = true;
    }
    
    Variable getUnitVar() const {
      return var;
    }
    
    void setFullyAssigned() {
      var = Variable::null;
      unit = true;      
    }
    
    bool isFullyAssigned() const {
      return unit && var.isNull();
    }
    
    void unsetUnit() {
      var = Variable::null;
      unit = false;
    }
  };
  
  /** Map from constraints to the unit information. */
  std::vector<unit_info> d_unitInfo;

  /** List of fixed variables to use for decisions x = c assertion */
  context::CDList<Variable> d_fixedVariables;

  /** Index of the last fixed variable */
  context::CDO<unsigned> d_fixedVariablesIndex;

  /** Number of fixed variable decisions */
  context::CDO<unsigned> d_fixedVariablesDecided;

  /** Last decided variable */
  Variable d_lastDecidedAndUnprocessed;

  /** Map from variables to constraints */
  std::vector<fm::LinearConstraint> d_constraints;

  /** Number of valid constraints */
  unsigned d_constraintsCount;
  
  /** Sum of sizes of constraints */
  unsigned d_constraintsSizeSum;
  
  /** Returns true if variable is a registered linear arith constraint */
  bool isLinearConstraint(Variable var) const {
    return var.typeIndex() == d_boolTypeIndex &&
      var.index() < d_constraints.size() &&
      !d_constraints[var.index()].isNull();
  }

  const fm::LinearConstraint& getLinearConstraint(Variable var) const {
    Assert(isLinearConstraint(var));
    return d_constraints[var.index()];
  }

  /** Is this variable an arithmetic variable */
  bool isArithmeticVariable(Variable var) const {
    return var.typeIndex() == d_realTypeIndex || var.typeIndex() == d_intTypeIndex;
  }

  /** Head pointer into the trail */
  context::CDO<size_t> d_trailHead;

  /** Bounds in the current context */
  fm::CDBoundsModel d_bounds;
  
  /** Watch manager for assigned variables */
  util::AssignedWatchManager d_assignedWatchManager;

  /** Checks whether the constraint is unit */
  bool isUnitConstraint(Variable constraint) const;

  /** Checks whether the constraint is fully assigned */
  bool isFullyAssigned(Variable constraint) const;

  /**
   * Takes a unit constraint (asserted or not) and processes it. If it is asserted then the appropriate bound
   * (if inequalities) is added, or adds to the list of dis-equalities for the free variable.
   */
  void processUnitConstraint(Variable constraint, SolverTrail::PropagationToken& out);

  /** Try the bounding and return the conflict if any. */
  Literal tryBounding(const fm::BoundingInfo& bounding, Variable var) const;

  /**
   * Propagate reason => propagation (x unassigned variable)
   */
  void propagateDeduction(Literal propagation, Literal reason, Variable x, SolverTrail::PropagationToken& out);

  /** Minimize the resolvent from the fmRule */
  void minimizeResolvent(std::set<Variable>& varsInvolved);

  /** The Fourier-Motzkin rule we use for derivation */
  rules::FourierMotzkinRule d_fmRule;

  /** The Fourier-Motzkin rule we use for derivation */
  rules::FourierMotzkinRuleDiseq d_fmRuleDiseq;

  /** Split rule for integers */
  rules::IntSplitRule d_splitRule;
  
  /**
   * Processes any conflicts.
   */
  void processConflicts(SolverTrail::PropagationToken& out);

  /** Bump the variables appearing in c */
  void bumpVariables(const fm::LinearConstraint& c);

  /** Bump the variables in the set */
  void bumpVariables(const std::set<Variable>& vars);

  /** Bump the variables in the set */
  void bumpVariables(const std::vector<Variable>& vars);
  
  /** Discriminator for constraints */
  fm::IConstraintDiscriminator* d_constraintDiscriminator;

  class SimpleReasonProvider : public SolverTrail::ReasonProvider {
    /** Propagation reasons */
    struct PropInfo {
      /** The assertion */
      Literal reason;
      /** Real variable to resolve */
      Variable x;
      PropInfo(Literal reason, Variable x)
      : reason(reason), x(x) {}
    };
    typedef context::CDInsertHashMap<Literal, PropInfo, LiteralHashFunction> reason_map;
    /** Reasons for propagations */
    reason_map d_reasons;
    /** The rule we're using */
    FMPlugin& d_plugin;
  public:
    SimpleReasonProvider(FMPlugin& plugin, context::Context* sc)
    : d_reasons(sc)
    , d_plugin(plugin)
    {}
    ~SimpleReasonProvider() {}
    /** Note a propagation */
    bool add(Literal propagation, Literal reason, Variable x);
    /** Explain */
    CRef explain(Literal l, SolverTrail::PropagationToken& out);
  } d_reasonProvider;

public:

  /** Constructor */
  FMPlugin(ClauseDatabase& clauseDb, const SolverTrail& trail, SolverPluginRequest& request, StatisticsRegistry* registry);

  ~FMPlugin();

  /** Perform propagation */
  void propagate(SolverTrail::PropagationToken& out);

  /** Perform a decision */
  void decide(SolverTrail::DecisionToken& out, Variable var);

  /** String representation of the plugin (for debug purposes mainly) */
  std::string toString() const;

  /** Notification of unset variables */
  void notifyBackjump(const std::vector<Variable>& vars);

  /** Mark phase of the GC */
  void gcMark(std::set<Variable>& varsToKeep, std::set<CRef>& clausesToKeep);

  /** Relocation phase of the GC */
  void gcRelocate(const VariableGCInfo& vReloc, const ClauseRelocationInfo& cReloc);

  void outputStatusHeader(std::ostream& out) const;
  void outputStatusLine(std::ostream& out) const;
};

// Register the plugin
MCSAT_REGISTER_PLUGIN(FMPlugin);

}
}



