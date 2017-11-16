#pragma once

#include "cvc4_private.h"

#include "expr/node.h"
#include "context/cdo.h"
#include "context/cdlist.h"
#include "util/statistics_registry.h"
#include "mcsat/util/selective_skolemization.h" //TODO REPLACEMENT

#include "mcsat/solver_trail.h"
#include "mcsat/clause/clause_db.h"
#include "mcsat/plugin/solver_plugin.h"
#include "mcsat/rules/resolution_rule.h"
#include "mcsat/util/var_priority_queue.h"

// possible replacment/redundancy? #include "smt/term_formula_removal.h"
#include "mcsat/util/ite_removal.h"

#include <unordered_map>
#include <unordered_set>


namespace CVC4 {
namespace mcsat {

/** Statistics for the bas Solver */
struct SolverStats {
  StatisticsRegistry* d_registry;
  /** Number of conflicts */
  IntStat conflicts;
  /** Number of decisions */
  IntStat decisions;
  /** Number of restarts */
  IntStat restarts;
  /** NUmber of GC calls */
  IntStat gc;
  
  SolverStats(StatisticsRegistry* registry)
  : d_registry(registry)
  , conflicts("mcsat::solver::conflicts", 0)
  , decisions("mcsat::solver::decisions", 0)
  , restarts("mcsat::solver::restarts", 0)
  , gc("mcsat::solver::gc", 0)
  {
    d_registry->registerStat(&conflicts);  
    d_registry->registerStat(&decisions);  
    d_registry->registerStat(&restarts);
    d_registry->registerStat(&gc);
  }
  
  ~SolverStats() {
    d_registry->unregisterStat(&conflicts);  
    d_registry->unregisterStat(&decisions);  
    d_registry->unregisterStat(&restarts);
    d_registry->unregisterStat(&gc);
  }
};

  
class Solver {

public:

  /** Construct the solver */
  Solver(context::UserContext* userContext, context::Context* searchContext);

  /** Destructor */
  virtual ~Solver();

  /** 
   * Assert the formula to the solver. If process is false the assertion will be
   * processed only after the call to check().
   * @param assertion the assertion
   * @param process true if to be processed as soon as possible 
   */
  void addAssertion(TNode assertion, bool process);

  /** Check if the current set of assertions is satisfiable */
  bool check();

  /** Add a plugin to the trail */
  void addPlugin(std::string plugin);

private:
 
  StatisticsRegistry* d_registry;

  /** Solver statistics */
  SolverStats d_stats;
  
  /** The variable database of the solver */
  VariableDatabase d_variableDatabase;

  /** Farm for all the clauses */
  ClauseFarm d_clauseFarm;

  /** The clause database for input clauses */
  ClauseDatabase& d_clauseDatabase;

  /** Main solver trail */
  SolverTrail d_trail;

  /** Rewritten Assertions */
  std::vector<Node> d_assertions;

  /** Minimize the conflicting literals below the level */
  void minimizeConflict(unsigned level);

  /** Resolution rule for conflict analysis */
  rules::BooleanResolutionRule d_rule_Resolution;

  /** Clauses learnt from conflicts */
  std::vector<CRef> d_learntClauses;

  /** All the plugins */
  std::vector<SolverPlugin*> d_plugins;

  /** Notification dispatch */
  NotificationDispatch d_notifyDispatch;
  
  /** Features dispatch (propagate, decide) */
  FeatureDispatch d_featuresDispatch;

  /** The requests of the plugins */
  std::vector<SolverPluginRequest*> d_pluginRequests;
  
  /** Process any requests from solvers */
  void processRequests();

  /** Perform propagation */
  void propagate(SolverTrail::PropagationToken::Mode mode);

  /** For analysis: Set of variables in the current resolvent that have a reason */
  variable_set d_varsWithReason;
  /** For analysis: Set of variables in the from the current level that we have seen alrady */
  variable_set d_varsSeen;

  /** Analyze all the conflicts in the trail */
  void analyzeConflicts();

  /** Has there been any requests */
  bool d_request;
  
  /** Has there been a backtrack request */
  bool d_backtrackRequested;

  /** The level of the backtrack request */
  size_t d_backtrackLevel;

  /** The clauses to be processed on backtrack */
  std::set<CRef> d_backtrackClauses;

  /** Will perform a backtrack in order to propagate/decide clause cRef at next appropriate time */
  void requestBacktrack(unsigned level, CRef cRef);
  
  /** Has a restart been requested */
  bool d_restartRequested;
  
  /** Has a GC run been requested */
  bool d_gcRequested;

  /** Request a search restart */
  void requestRestart();
  
  /** Request a propagation round */
  void requestPropagate();

  /** Request garbage collection at next restart */
  void requestGC();

  /** Perform garbage collection */
  void performGC();

  friend class SolverPluginRequest;

  /** Priority queue for variable selection */
  util::VariablePriorityQueue d_variableQueue;

  class NewVariableNotify : public VariableDatabase::INewVariableNotify {
    util::VariablePriorityQueue& d_queue;
  public:
    NewVariableNotify(util::VariablePriorityQueue& d_queue);
    void newVariable(Variable var);
  } d_newVariableNotify;

  /** Bump the variable value */
  void bump(Variable var, unsigned amount) {
    d_variableQueue.bumpVariable(var, amount);
  }

  /** Scores of learnt clauses */
  std::unordered_map<CRef, double, CRefHashFunction> d_learntClausesScore;

  /** Maximal score */
  double d_learntClausesScoreMax;

  /** Increase per bump */
  double d_learntClausesScoreIncrease;

  /** Maximal score before we scale */
  double d_learntClausesScoreMaxBeforeScaling;

  /** Decay of clause scores */
  double d_leanrtClausesScoreDecay;

  void decayClauseScores() { d_learntClausesScoreIncrease *= (1 / d_leanrtClausesScoreDecay); }

  /** Increase the clause heuristic */
  void bumpClause(CRef cRef);

  /** Heuristically remove some learnt clauses */
  void shrinkLearnts();

  /** Limit for the learnt clauses */
  unsigned d_learntsLimit;

  /** Learn limit increase */
  double d_learntsLimitInc;

  /** Output a status line */
  void outputStatusLine(bool header) const;

  /** ITE Removal */
  RemoveITE d_removeITE;

  /**
   * Class responsible for traversing the input formulas and registering variables
   * with the variable database.
   */
  class VariableRegister {

    /** Variable database we're using */
    VariableDatabase& d_varDb;

    /** Set of already visited nodes */
    std::unordered_set<TNode, TNodeHashFunction> d_visited;

    /** The list of all variables */
    std::vector<Variable> d_variables;
    
  public:

    typedef void return_type;

    VariableRegister(VariableDatabase& varDb)
    : d_varDb(varDb) {}

    bool alreadyVisited(TNode current, TNode parent) const {
      return d_visited.find(current) != d_visited.end();
    }

    void visit(TNode current, TNode parent);
    void start(TNode node) {}
    void done(TNode node) {}
    
    std::vector<Variable>& getVariables() {
      return d_variables;
    }
  } d_variableRegister;
  
  /** Runner for skolemization of shared terms */
  SkolemizationRunner d_purifyRunner;

};

}
}




