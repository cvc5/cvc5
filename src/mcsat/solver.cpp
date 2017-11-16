#include "solver.h"

#include "options/mcsat_options.h"
#include "mcsat/rules/proof_rule.h"
#include "mcsat/plugin/solver_plugin_factory.h"

#include "theory/theory.h"
#include "theory/rewriter.h"
#include "smt_util/node_visitor.h"
#include "smt/smt_statistics_registry.h"

#include <algorithm>

using namespace std;

using namespace CVC4;
using namespace CVC4::mcsat;

template<typename T>
class ScopedValue {
  T& d_toWatch;
  T d_oldValue;
public:
  ScopedValue(T& toWatch, T newValue)
  : d_toWatch(toWatch)
  , d_oldValue(toWatch)
  {
    toWatch = newValue;
  }
  ~ScopedValue() {
    d_toWatch = d_oldValue;
  } 
};

void Solver::VariableRegister::visit(TNode current, TNode parent) {
  if (current.isVar()) {
    // We register the variables
    Variable var = d_varDb.getVariable(current);
    d_variables.push_back(var);
  } else {
    // we also register any cross-theory terms as variables
    // f(x) -> variable, uf/int
    // f(x + y) ->  NOT POSSIBLE (WE PURIFY)
    // a < b -> variable arith/bool
    // a = b -> variable builtin/bool
    // x + y -> not, arith/arith
    theory::TheoryId id1 = theory::kindToTheoryId(current.getKind());
    theory::TheoryId id2 = theory::Theory::theoryOf(current.getType());
    if (id1 != id2) {
      Variable var = d_varDb.getVariable(current);
      d_variables.push_back(var);
    }
  }
  d_visited.insert(current);      
}
  
  
Solver::NewVariableNotify::NewVariableNotify(util::VariablePriorityQueue& queue)
: VariableDatabase::INewVariableNotify(false)
, d_queue(queue)
{}

void Solver::NewVariableNotify::newVariable(Variable var) {
  d_queue.newVariable(var);
}

Solver::Solver(context::UserContext* userContext, context::Context* searchContext) 
: d_registry(smtStatisticsRegistry())
, d_stats(d_registry) 
, d_variableDatabase(searchContext)
, d_clauseFarm(searchContext)
, d_clauseDatabase(d_clauseFarm.newClauseDB("problem_clauses"))
, d_trail(searchContext)
, d_rule_Resolution(d_clauseDatabase, d_trail, d_registry)
, d_featuresDispatch(d_trail)
, d_request(false)
, d_backtrackRequested(false)
, d_backtrackLevel(0)
, d_restartRequested(false)
, d_gcRequested(false)
, d_newVariableNotify(d_variableQueue)
, d_learntClausesScoreMax(1.0)
, d_learntClausesScoreIncrease(1.0)
, d_learntClausesScoreMaxBeforeScaling(1e20)
, d_leanrtClausesScoreDecay(0.95)
, d_learntsLimit(100)
, d_learntsLimitInc(options::mcsat_learnts_limit_inc())
, d_removeITE(userContext)
, d_variableRegister(d_variableDatabase)
, d_purifyRunner(userContext) 
{
  // Repeatable
  srand(0);

  d_variableDatabase.addNewVariableListener(&d_newVariableNotify);

  // Add some engines
  addPlugin("CVC4::mcsat::CNFPlugin");
  addPlugin("CVC4::mcsat::UFPlugin");
  addPlugin("CVC4::mcsat::FMPlugin");
  addPlugin("CVC4::mcsat::BCPEngine");
}

Solver::~Solver() {
  for (unsigned i = 0; i < d_plugins.size(); ++ i) {
    delete d_plugins[i];
    delete d_pluginRequests[i];
  }
}

void Solver::addAssertion(TNode assertion, bool process) {
  VariableDatabase::SetCurrent scoped(&d_variableDatabase);
  Debug("mcsat::solver") << "Solver::addAssertion(" << assertion << ")" << endl; 

  // Remove ITEs
  IteSkolemMap skolemMap;
  std::vector<Node> assertionVector;
  assertionVector.push_back(assertion);
  d_removeITE.run(assertionVector, skolemMap);

  // Normalize
  for (unsigned i = 0; i < assertionVector.size(); ++ i) {
    assertionVector[i] = theory::Rewriter::rewrite(assertionVector[i]);
  }


  //TODO figure out what this is supposed to be, if anything

  // Purify any shared terms 
  d_purifyRunner.run(assertionVector);
  
  // Normalize
  for (unsigned i = 0; i < assertionVector.size(); ++ i) {
    assertionVector[i] = theory::Rewriter::rewrite(assertionVector[i]);
  }

  for (unsigned i = 0; i < assertionVector.size(); ++ i) {
    // Normalize and remember
    Debug("mcsat::assertions") << "Solver::addAssertion(): " << assertionVector[i] << endl; 
    TNode assertion = assertionVector[i];
    d_assertions.push_back(assertion);

    // Register all the variables wit the database
    NodeVisitor<VariableRegister>::run(d_variableRegister, assertion);

    // Notify the plugins about the new assertion
    d_notifyDispatch.notifyAssertion(assertion);

    // Run propagation immediately if requested
    if (process) {
      // Propagate the added clauses
      propagate(SolverTrail::PropagationToken::PROPAGATION_INIT);
    }
  }
}

void Solver::processRequests() {

  if (d_backtrackRequested) {
    Debug("mcsat::solver") << "Solver::processBacktrackRequests()" << std::endl;

    // Pop to the requested level
    std::vector<Variable> variablesUnset;
    d_trail.popToLevel(d_backtrackLevel, variablesUnset);

    // Add the variables to the variable queue
    for (unsigned i = 0; i < variablesUnset.size(); ++ i) {
      Variable var = variablesUnset[i];
      if (!d_variableQueue.inQueue(var)) {
        d_variableQueue.enqueue(var);
      }
    }

    // Notify the plugins about the backjump variables
    d_notifyDispatch.notifyBackjump(variablesUnset);

    // Decay the scores in the queue
    d_variableQueue.decayScores();
    
    // All backtrack clauses are to the same level, but some might propagate and some are decision inducing clauses.
    // If there any propagating clauses, we just do the propagations to ensure progress.
    bool somePropagates = false;
    std::vector<bool> propagates;
    std::set<CRef>::iterator it = d_backtrackClauses.begin();
    for (; it != d_backtrackClauses.end(); ++ it) {
      Clause& clause = it->getClause();
      Debug("mcsat::solver") << "Solver::processBacktrackRequests(): processing " << clause << std::endl;
      if (clause.size() == 1 || d_trail.isFalse(clause[1])) {
        propagates.push_back(true);
        somePropagates = true;
	Debug("mcsat::solver") << "Solver::processBacktrackRequests(): propagates" << std::endl;
      } else {
        propagates.push_back(false);
	Debug("mcsat::solver") << "Solver::processBacktrackRequests(): doesn't propagates " << std::endl;
      }
    }

    if (somePropagates) {
      Debug("mcsat::solver") << "Solver::processBacktrackRequests(): we have a propagation" << std::endl;
      // Propagate all the added clauses that propagate
      std::set<CRef>::iterator it = d_backtrackClauses.begin();
      SolverTrail::PropagationToken propagate(d_trail, SolverTrail::PropagationToken::PROPAGATION_INIT);
      for (unsigned i = 0; it != d_backtrackClauses.end(); ++ it, ++ i) {
        if (propagates[i]) {
          Clause& clause = it->getClause();
          propagate(clause[0], *it);
        }
      }
    } else {
      Debug("mcsat::solver") << "Solver::processBacktrackRequests(): we do a decision" << std::endl;
      // Decision token
      SolverTrail::DecisionToken decide(d_trail);

      // Pick the literals for the decision
      Literal toDecide;
      double toDecideScore = -1;
      Clause& c = d_backtrackClauses.begin()->getClause();

      for (unsigned i = 0; i < c.size(); ++ i) {
        if (d_trail.hasValue(c[i].getVariable())) {
          Assert(d_trail.isFalse(c[i]));
        } else {
          double score = d_variableQueue.getScore(c[i].getVariable());
          if (score > toDecideScore) {
            toDecideScore = score;
            toDecide = c[i];
          }
        }
      }
      decide(toDecide);
    }

    // Clear the requests TODO: remove
    d_backtrackRequested = false;
    d_backtrackClauses.clear();
  }
  
  if (d_restartRequested) {

    std::vector<Variable> variablesUnset;
    // Restart to level 0
    d_trail.popToLevel(0, variablesUnset);
    // Notify of backjump
    d_notifyDispatch.notifyBackjump(variablesUnset);
    // Notify of the restart 
    d_notifyDispatch.notifyRestart();

    // Add the variables to the variable queue
    for (unsigned i = 0; i < variablesUnset.size(); ++ i) {
      Variable var = variablesUnset[i];
      if (!d_variableQueue.inQueue(var)) {
        d_variableQueue.enqueue(var);
      }
    }

    if (d_gcRequested) {
      performGC();
      d_learntsLimit *= d_learntsLimitInc;
    }
    
    d_restartRequested = false;
    d_gcRequested = false;
    ++ d_stats.restarts;

    outputStatusLine(d_stats.restarts.getData() % 100 == 0);

    if (Debug.isOn("mcsat::solver::unit")) {
      Debug("mcsat::solver::unit") << d_trail << std::endl;
    }
  }

  // Requests have been processed
  d_request = false;
}

void Solver::requestRestart() {
  d_request = true;
  d_restartRequested = true;
}

void Solver::requestPropagate() {
  d_request = true;
}

void Solver::requestGC() {
  d_gcRequested = true;
  requestRestart();
}


void Solver::requestBacktrack(unsigned level, CRef cRef) {
  Assert(level < d_trail.decisionLevel(), "Don't try to fool backtracking to do your propagation");

  Debug("mcsat::solver") << "Solver::requestBacktrack(" << level << ", " << cRef << ")" << std::endl;

  if (!d_backtrackRequested) {
    // First time request
    d_backtrackLevel = level;
  } else {
    if (d_backtrackLevel > level) {
      // Even lower backtrack
      d_backtrackLevel = level;
      d_backtrackClauses.clear();
    }
  }

  // Interrupt the dispatch
  d_featuresDispatch.interrupt();

  d_request = true;
  d_backtrackRequested = true;
  d_backtrackClauses.insert(cRef);
}


void Solver::propagate(SolverTrail::PropagationToken::Mode mode) {
  Debug("mcsat::solver") << "Solver::propagate(" << mode << ")" << std::endl;

  bool propagationDone = false;
  while (d_trail.consistent() && !d_request && !propagationDone) {
    // Token for the plugins to propagate at
    SolverTrail::PropagationToken propagationOut(d_trail, mode);
    // Let all plugins propagate
    d_featuresDispatch.propagate(propagationOut);
    // If the token wasn't used, we're done
    propagationDone = !propagationOut.used();
  }
}

bool Solver::check() {
  
  outputStatusLine(true);

  /** Initial limit on the number of learnt clauses */
  d_learntsLimit = d_clauseDatabase.size();

  Debug("mcsat::solver::search") << "Solver::check()" << std::endl;

  // Search while not all variables assigned 
  while (true) {
    
    // If a backtrack was requested then
    processRequests();

    // Normal propagate
    propagate(SolverTrail::PropagationToken::PROPAGATION_NORMAL);

    // If inconsistent, perform conflict analysis
    if (!d_trail.consistent()) {

      Debug("mcsat::solver::search") << "Solver::check(): Conflict" << std::endl;
      Debug("mcsat::trail") << d_trail << std::endl;
     
      ++ d_stats.conflicts;
      decayClauseScores();
      
      // Notify of a new conflict situation
      d_notifyDispatch.notifyConflict();
      
      // If the conflict is at level 0, we're done
      if (d_trail.decisionLevel() == 0) {
        return false;
      }

      // Analyze the conflict
      analyzeConflicts();

      // Are we too smart?
      if (d_learntClauses.size() > d_learntsLimit) {
        requestGC();
      }

      // Start over with propagation
      continue;
    }
    
    // Process any requests
    if (d_request) {
      continue;
    }

    // Clauses processed, propagators done, we're ready for a decision
    SolverTrail::DecisionToken decisionOut(d_trail);
    Debug("mcsat::solver::search") << "Solver::check(): trying decision" << std::endl;

    Variable toDecide;
    while (!d_variableQueue.empty()) {

      double selectRand = ((double)rand()) / RAND_MAX;

      if (selectRand < options::mcsat_var_random_select()) {
        toDecide = d_variableQueue.getRandom();
      } else {
        toDecide = d_variableQueue.pop();
      }

      if (!d_trail.hasValue(toDecide)) {
        break;
      } else {
        toDecide = Variable::null;
      }

    }

    if (!toDecide.isNull()) {
      d_featuresDispatch.decide(decisionOut, toDecide);
      Assert(decisionOut.used());
      if (d_trail[d_trail.size() - 1].var != toDecide && !d_variableQueue.inQueue(toDecide)) {
        d_variableQueue.enqueue(toDecide);
      }
      // We made a new decision
      ++ d_stats.decisions;
    } else {
      Debug("mcsat::solver::search") << "Solver::check(): no decisions, doing fullcheck" << std::endl;
      // Do complete propagation
      propagate(SolverTrail::PropagationToken::PROPAGATION_COMPLETE);
      // If no-one has anything to say, we're done
      if (!d_request) {
	break;
      }
    }
  }

  // Since we're here, we're satisfiable
  if (Debug.isOn("mcsat::model")) {
    const std::vector<Variable>& vars = d_variableRegister.getVariables();
    for (unsigned i = 0; i < vars.size(); ++ i) {
      Debug("mcsat::model") << vars[i] << "\t->\t" << d_trail.value(vars[i]) << std::endl; 
    }
  }
  
  return true;
}

void Solver::addPlugin(std::string pluginId) {

  d_pluginRequests.push_back(new SolverPluginRequest(this));
  SolverPlugin* plugin = SolverPluginFactory::create(pluginId, d_clauseDatabase, d_trail, *d_pluginRequests.back(), d_registry);
  d_plugins.push_back(plugin);
  d_notifyDispatch.addPlugin(plugin);
  d_featuresDispatch.addPlugin(plugin);

  Notice() << "mcsat::Solver: added plugin " << *plugin << std::endl;
}

void Solver::analyzeConflicts() {

  // Conflicts to resolve
  std::vector<SolverTrail::InconsistentPropagation> conflicts;
  d_trail.getInconsistentPropagations(conflicts);

  Assert(conflicts.size() > 0);
  Debug("mcsat::solver::analyze") << "Solver::analyzeConflicts()" << std::endl;

  for (unsigned c = 0; c < conflicts.size(); ++ c) {

    Assert(d_varsWithReason.size() == 0);
    Assert(d_varsSeen.size() == 0);

    // Get the current conflict
    SolverTrail::InconsistentPropagation& conflictPropagation = conflicts[c];

    // Clause in conflict
    Clause& conflictingClause = conflictPropagation.reason.getClause();
    Debug("mcsat::solver::analyze") << "Solver::analyzeConflicts(): analyzing " << conflictingClause << std::endl;

    // This is a useful clause
    if (conflictingClause.getRuleId() == d_rule_Resolution.getRuleId()) {
      bumpClause(conflictPropagation.reason);
    }

    // The level at which the clause is in conflict
    unsigned conflictLevel = 0;
    for (unsigned i = 0; i < conflictingClause.size(); ++ i) {
      conflictLevel = std::max(conflictLevel, d_trail.decisionLevel(conflictingClause[i].getVariable()));
    }
    Debug("mcsat::solver::analyze") << "Solver::analyzeConflicts(): in conflict at level " << conflictLevel << std::endl;
    Debug("mcsat::solver::analyze") << "Solver::analyzeConflicts(): trail: " << d_trail << std::endl;

    // The Boolean resolution rule
    d_rule_Resolution.start(conflictPropagation.reason);
    d_notifyDispatch.notifyConflictResolution(conflictPropagation.reason);
    
    // Number of literals in the current resolvent
    unsigned varsAtConflictLevel = 0;

    // Setup the initial variable info
    for (unsigned i = 0; i < conflictingClause.size(); ++ i) {
      Literal lit = conflictingClause[i];
      Variable var = lit.getVariable();
      // We resolve literals at the conflict level
      if (d_trail.decisionLevel(var) == conflictLevel) {
        if (!d_varsSeen.contains(var)) {
          varsAtConflictLevel ++;
          d_varsSeen.insert(var);
          if (d_trail.hasReason(~lit)) {
            d_varsWithReason.insert(var);
          }
        }
      }
    }

    // Resolve out all literals at the top level
    Assert(d_trail.size(conflictLevel) >= 1);
    unsigned trailIndex = d_trail.size(conflictLevel) - 1;

    // While there is more than one literal at current conflict level (UIP)
    while (!d_trail[trailIndex].isDecision() && varsAtConflictLevel > 1) {

      Debug("mcsat::solver::analyze") << "Solver::analyzeConflicts(): can be resolved: " << d_varsWithReason << std::endl;
      Debug("mcsat::solver::analyze") << "Solver::analyzeConflicts(): seen: " << d_varsSeen << std::endl;
      Debug("mcsat::solver::analyze") << "Solver::analyzeConflicts(): at index " << trailIndex << std::endl;

      // Find the next literal to resolve
      while (!d_trail[trailIndex].isDecision() && !d_varsWithReason.contains(d_trail[trailIndex].var)) {
        -- trailIndex;
      }

      // If we hit the decision then it must be either a UIP or a semantic decision
      if (d_trail[trailIndex].isDecision()) {
        Assert(d_trail[trailIndex].type == SolverTrail::SEMANTIC_DECISION || varsAtConflictLevel == 1);
        break;
      }

      // We can resolve the variable, so let's do it
      Variable varToResolve = d_trail[trailIndex].var;
      Debug("mcsat::solver::analyze") << "Solver::analyzeConflicts(): resolving: " << varToResolve << " at " << trailIndex << std::endl;

      // If the variable is false, take the negated literal
      Literal literalToResolve(varToResolve, d_trail.isFalse(varToResolve));

      // Get the reason of the literal
      CRef literalReason = d_trail.reason(literalToResolve);
      Clause& literalReasonClause = literalReason.getClause();
      Assert(literalReasonClause[0].getVariable() == varToResolve);

      // Resolve the literal (propagations should always have first literal propagating)
      Assert(literalReasonClause[0].getVariable() == varToResolve);
      d_rule_Resolution.resolve(literalReason, 0);
      d_notifyDispatch.notifyConflictResolution(literalReason);
      if (literalReasonClause.getRuleId() == d_rule_Resolution.getRuleId()) {
        bumpClause(literalReason);
      }

      // We removed one literal
      -- varsAtConflictLevel;

      // Update the info for the resolved literals
      Assert(literalReasonClause[0].getVariable() == varToResolve);
      for (unsigned i = 1; i < literalReasonClause.size(); ++ i) {
	Literal lit = literalReasonClause[i];
        Variable var = lit.getVariable();
        Debug("mcsat::solver::analyze") << "Solver::analyzeConflicts(): checking reason lit: " << lit << " at " << d_trail.decisionLevel(var) << std::endl;
        // We resolve literals at the conflict level
        if (d_trail.decisionLevel(var) == conflictLevel) {
          Debug("mcsat::solver::analyze") << "Solver::analyzeConflicts(): checking reason var: " << (d_varsSeen.contains(var) ? "seen" : "unseen") << std::endl;
          if (!d_varsSeen.contains(var)) {
            varsAtConflictLevel ++;
            d_varsSeen.insert(var);
            if (d_trail.hasReason(~lit)) {
              d_varsWithReason.insert(var);
            }
          }
        }
      }

      // Done with this trail element
      -- trailIndex;
    }

    // Try minimization
    if (options::mcsat_conflict_minimization()) {
      minimizeConflict(conflictLevel);
    }

    // Clear the data
    d_varsWithReason.clear();
    d_varsSeen.clear();

    // Finish the resolution
    CRef resolvent = d_rule_Resolution.finish();
    Debug("mcsat::solver::analyze") << "Solver::analyzeConflicts(): resolvent: " << resolvent << std::endl;

    if (resolvent.getClause().size() > 1 && resolvent.getClause().getRuleId() == d_rule_Resolution.getRuleId()) {
      // If this is a new clause, so we manage it's deletion
      d_learntClausesScore[resolvent] = d_learntClausesScoreMax;
      d_learntClauses.push_back(resolvent);
    } 
    
    // If number of variables in the resolvent is > 1, it must be that these 
    // literals are semantically true. This also means that the clause 
    // propagates at the conflict level, and we can't resolve the literals.
    // So, we go back and decide one of them 
    if (varsAtConflictLevel > 1) {
      Assert(d_trail[trailIndex].type == SolverTrail::SEMANTIC_DECISION);
      requestBacktrack(conflictLevel - 1, resolvent);
    }
  }
}

void Solver::bumpClause(CRef cRef) {
  std::unordered_map<CRef, double, CRefHashFunction>::iterator find = d_learntClausesScore.find(cRef);
  
  if (find == d_learntClausesScore.end()) {
    return;
  }

  find->second += d_learntClausesScoreIncrease;

  if (find->second > d_learntClausesScoreMax) {
    d_learntClausesScoreMax = find->second;
  }

  if (find->second > d_learntClausesScoreMaxBeforeScaling) {
    std::unordered_map<CRef, double, CRefHashFunction>::iterator it = d_learntClausesScore.begin();
    std::unordered_map<CRef, double, CRefHashFunction>::iterator it_end = d_learntClausesScore.begin();
    for (; it != it_end; ++ it)  {
      it->second /= d_learntClausesScoreMaxBeforeScaling;
    }
    d_learntClausesScoreMax /= d_learntClausesScoreMaxBeforeScaling;
    d_learntClausesScoreIncrease /= d_learntClausesScoreMaxBeforeScaling;
  }
}

struct learnt_cmp_by_score {

  const std::unordered_map<CRef, double, CRefHashFunction>& d_scoreMap;

  learnt_cmp_by_score(const std::unordered_map<CRef, double, CRefHashFunction>& map)
  : d_scoreMap(map)
  {}

  bool operator () (const CRef& c1, const CRef& c2) const {
    // Prefer better score
    return d_scoreMap.find(c1)->second > d_scoreMap.find(c2)->second;
  }

};

void Solver::shrinkLearnts() {
  d_trail.removeSatisfied(d_learntClauses);
  learnt_cmp_by_score cmp(d_learntClausesScore);
  std::sort(d_learntClauses.begin(), d_learntClauses.end(), cmp);
  // Keep all clauses in size/2 + clauses of size <= 2
  unsigned toKeep = d_learntClauses.size() * options::mcsat_learnts_keep_factor();
  for (unsigned i = 0; i < d_learntClauses.size(); ++ i) {
    Clause& clause = d_learntClauses[i].getClause();
    
    bool keep = false;
    if (i < toKeep && clause.size() > 1) {
      toKeep = true;
    } else if (clause.size() == 2) {
      toKeep = true;
    }
    
    if (keep) {
      d_learntClauses[toKeep ++] = d_learntClauses[i];
    }
  }
  d_learntClauses.resize(toKeep);
}

void Solver::performGC() {

  ++ d_stats.gc;

  // Shrink learnt clauses we care about
  shrinkLearnts();

  // List of clauses to keep
  std::set<CRef> clausesToKeep;
  // List of variables to keep
  std::set<Variable> variablesToKeep;

  // Input variables
  Debug("mcsat::gc") << "GC: adding input variables" << std::endl;
  std::vector<Variable>& inputVariables = d_variableRegister.getVariables();
  variablesToKeep.insert(inputVariables.begin(), inputVariables.end());
  Assert(variablesToKeep.count(Variable::null) == 0);

  // Learnt clauses we decide to keep
  Debug("mcsat::gc") << "GC: adding learnts" << std::endl;
  clausesToKeep.insert(d_learntClauses.begin(), d_learntClauses.end());
  Assert(clausesToKeep.count(CRef::null) == 0);

  // Ask the trail
  Debug("mcsat::gc") << "GC: marking with the trail" << std::endl;
  d_trail.gcMark(variablesToKeep, clausesToKeep);
  Assert(variablesToKeep.count(Variable::null) == 0);
  Assert(clausesToKeep.count(CRef::null) == 0);

  // Dispatch marking to the plugins
  for(unsigned i = 0; i < d_plugins.size(); ++ i) {
    // List of clauses to keep
    std::set<CRef> p_clausesToKeep;
    // List of variables to keep
    std::set<Variable> p_variablesToKeep;
    // Ask the plugin
    Debug("mcsat::gc") << "GC: marking with" << *d_plugins[i] << std::endl;
    d_plugins[i]->gcMark(p_variablesToKeep, p_clausesToKeep);
    // Remember
    variablesToKeep.insert(p_variablesToKeep.begin(), p_variablesToKeep.end());
    clausesToKeep.insert(p_clausesToKeep.begin(), p_clausesToKeep.end());
    Assert(variablesToKeep.count(Variable::null) == 0);
    Assert(clausesToKeep.count(CRef::null) == 0);
  }

  // Go through the clauses and get the variables
  Debug("mcsat::gc") << "GC: collecting variables from clauses" << std::endl;
  std::set<CRef>::const_iterator c_it = clausesToKeep.begin();
  std::set<CRef>::const_iterator c_it_end = clausesToKeep.end();
  for (; c_it != c_it_end; ++ c_it) {
    Clause& clause = (*c_it).getClause();
    for (unsigned i = 0; i < clause.size(); ++ i) {
      variablesToKeep.insert(clause[i].getVariable());
    }
  }
  Assert(variablesToKeep.count(Variable::null) == 0);
  Assert(clausesToKeep.count(CRef::null) == 0);

  // Do the clause GC
  Debug("mcsat::gc") << "GC: clause database" << std::endl;
  ClauseRelocationInfo clauseRelocationInfo;
  d_clauseFarm.performGC(clausesToKeep, clauseRelocationInfo);

  // Do the variable GC
  Debug("mcsat::gc") << "GC: variable database" << std::endl;
  VariableGCInfo variableRelocationInfo;
  d_variableDatabase.performGC(variablesToKeep, variableRelocationInfo);

  // Clauses
  clauseRelocationInfo.relocate(d_learntClauses);
  // Clause scores
  std::unordered_map<CRef, double, CRefHashFunction> learntClausesScoreNew;
  std::unordered_map<CRef, double, CRefHashFunction>::const_iterator s_it = d_learntClausesScore.begin();
  std::unordered_map<CRef, double, CRefHashFunction>::const_iterator s_it_end = d_learntClausesScore.end();
  for (; s_it != s_it_end; ++ s_it) {
    CRef refNew = clauseRelocationInfo.relocate(s_it->first);
    if (!refNew.isNull()) {
      learntClausesScoreNew[refNew] = s_it->second;
    }
  }
  learntClausesScoreNew.swap(d_learntClausesScore);

  // Relocate the variable queue
  d_variableQueue.gcRelocate(variableRelocationInfo);

  // The trail
  Debug("mcsat::gc") << "GC: relocating trail" << std::endl;
  d_trail.gcRelocate(variableRelocationInfo, clauseRelocationInfo);
  for (unsigned i = 0; i < d_plugins.size(); ++ i) {
    Debug("mcsat::gc") << "GC: relocating " << *d_plugins[i] << std::endl;
    d_plugins[i]-> gcRelocate(variableRelocationInfo, clauseRelocationInfo);
  }
}

void Solver::outputStatusLine(bool header) const {
  
  if (!Notice.isOn()) {
    return;
  }
  
  if (header) {
    Notice()
        << setw(10) << "Variables"
        << setw(10) << "Clauses"
        << setw(10) << "Restarts"
        << setw(10) << "Conflicts"
        << setw(10) << "Trail"
        << setw(10) << "T/V";   
    d_featuresDispatch.outputStatusHeader(Notice());
    Notice() << std::endl;
  }
  Notice()
    << setw(10) << d_variableDatabase.size()
    << setw(10) << d_clauseDatabase.size()
    << setw(10) << d_stats.restarts.getData()
    << setw(10) << d_stats.conflicts.getData()
    << setw(10) << d_trail.size()
    << setw(10) << setprecision(4) << (double)d_trail.size()/d_variableDatabase.size();

  d_featuresDispatch.outputStatusLine(Notice());
  Notice() << std::endl;
}

void Solver::minimizeConflict(unsigned level) {
  // Reuse the seen vector
  d_varsSeen.clear();

  // Get the literals in the resolvent
  std::vector<Literal> lits;
  std::set<unsigned> levels;
  d_rule_Resolution.getLiterals(lits);

  // Mark the literals and levels we care about
  unsigned keep = 0;
  for (unsigned i = 0; i < lits.size(); ++ i) {
    Literal lit = lits[i];
    Variable var = lit.getVariable();
    unsigned varLevel = d_trail.decisionLevel(var);
    if (varLevel > 0 && varLevel < level && d_trail.hasClausalReason(~lit)) {
      d_varsSeen.insert(var);
      levels.insert(varLevel);
      lits[keep ++] = lit;
    }
  }
  lits.resize(keep);

  // Check if any of the literals is redundant
  for (unsigned i = 0; i < lits.size(); ++ i) {

    Literal lit = ~lits[i];             // Literal to try and resolve out
    std::vector<Variable> varsSeenUndo; // Vars to undo in the seen vector

    // Resolution queue contains the implied (true) literals that need to be resolved
    std::vector<Literal> resolutionQueue;
    resolutionQueue.push_back(lit);

    // Check if this literal is redundant
    bool redundant = true;
    for (unsigned current = 0; redundant && current < resolutionQueue.size(); ++ current) {
      Literal currentLiteral = resolutionQueue[current];
      Assert(d_trail.hasClausalReason(currentLiteral));
      // Reason for the literal
      Clause& currentReason = d_trail.reason(currentLiteral).getClause();
      Assert(currentReason[0] == currentLiteral);
      for (unsigned i = 1; i < currentReason.size(); ++ i) {
        Literal lit = ~currentReason[i];
        Variable var = lit.getVariable();
        unsigned level = d_trail.decisionLevel(var);
        if (!d_varsSeen.contains(var) && level > 0) {
          // Potentially not redundant
          if (d_trail.hasClausalReason(lit) && levels.count(level) > 0) {
            // Lets keep trying
            d_varsSeen.insert(var);
            resolutionQueue.push_back(lit);
            varsSeenUndo.push_back(var);
          } else{
            // Quit
            redundant = false;
            break;
          }
        }
      }
    }

    if (!redundant) {
      // Not redundant, we keep it and clear the data
      for (unsigned i = 0; i < varsSeenUndo.size(); ++ i) {
        d_varsSeen.remove(varsSeenUndo[i]);
      }
    } else {
      // Redundant, keep the seen data and perform the resolution
      for (unsigned current = 0; current < resolutionQueue.size(); ++ current) {
        Literal currentLiteral = resolutionQueue[current];
        if (d_trail.decisionLevel(currentLiteral.getVariable()) > 0) {
          d_rule_Resolution.resolve(d_trail.reason(currentLiteral), 0);
        }
      }
    }

    varsSeenUndo.clear();
  }

  // Clear the seen vector
  d_varsSeen.clear();
}
