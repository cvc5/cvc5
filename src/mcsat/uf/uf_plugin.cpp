#include "mcsat/uf/uf_plugin.h"
#include "mcsat/options.h"

using namespace CVC4;
using namespace mcsat;
using namespace util;

UFPlugin::NewVariableNotify::NewVariableNotify(UFPlugin& plugin)
: INewVariableNotify(false)
, d_plugin(plugin)
{
}

void UFPlugin::NewVariableNotify::newVariable(Variable var) {
  // Register arithmetic constraints
  TNode varNode = var.getNode();
  switch(varNode.getKind()) {
  case kind::APPLY_UF:
    d_plugin.newUninterpretedFunction(var);
    break;
  default:
    // Ignore
    break;
  }
}

UFPlugin::UFPlugin(ClauseDatabase& database, const SolverTrail& trail, SolverPluginRequest& request)
: SolverPlugin(database, trail, request)
, d_newVariableNotify(*this)
, d_trailHead(trail.getSearchContext(), 0)
, d_valueMap(trail.getSearchContext())
, d_appEvaluation(trail.getSearchContext())
, d_ackermannRule(database, trail)
{
  Debug("mcsat::uf") << "UFPlugin::UFPlugin()" << std::endl;

  // We decide values of variables and can detect conflicts
  addFeature(CAN_PROPAGATE);

  // Notifications we need
  addNotification(NOTIFY_BACKJUMP);

  // Add the listener
  VariableDatabase::getCurrentDB()->addNewVariableListener(&d_newVariableNotify);
}

std::string UFPlugin::toString() const  {
  return "Uninterpreted Functions (Model-Based)";
}

class var_assign_compare {
  const SolverTrail& d_trail;
public:
  var_assign_compare(const SolverTrail& trail)
  : d_trail(trail) {}

  bool operator () (const Variable& v1, const Variable& v2) {

    bool v1_hasValue = d_trail.hasValue(v1);
    bool v2_hasValue = d_trail.hasValue(v2);

    // Two unassigned literals are sorted arbitrarily
    if (!v1_hasValue && !v2_hasValue) {
      return v1 < v2;
    }

    // Unassigned variables are put to front
    if (!v1_hasValue) return true;
    if (!v2_hasValue) return false;

    // Both are assigned, we compare by trail index
    return d_trail.decisionLevel(v1) > d_trail.decisionLevel(v2);
  }
};

void UFPlugin::newUninterpretedFunction(Variable f_app) {
  Debug("mcsat::uf") << "UFPlugin::newUninterpretedFunction(" << f_app << ")" << std::endl;
  
  // The actuall node
  TNode node = f_app.getNode();
  Assert(node.getKind() == kind::APPLY_UF);
  
  // Get the variables of the constraint
  std::vector<Variable> vars;
  for (unsigned i = 0; i < node.getNumChildren(); ++ i) {
    if (!node[i].isConst()) {
      Assert(VariableDatabase::getCurrentDB()->hasVariable(node[i]));
      vars.push_back(VariableDatabase::getCurrentDB()->getVariable(node[i]));
    }
  }

  if (vars.size() > 0) {
    // Sort the variables by trail assignment index (if any)
    var_assign_compare cmp(d_trail);
    std::sort(vars.begin(), vars.end(), cmp);

    // Eliminate duplicates
    unsigned keep = 1;
    for (unsigned i = 1; i < vars.size(); ++ i) {
      if (vars[i] != vars[i-1]) {
        vars[keep ++] = vars[i];
      }
    }
    vars.resize(keep);

    // Add the variable list to the watch manager and watch the first two constraints
    VariableListReference listRef = d_assignedWatchManager.newListToWatch(vars, f_app);
    VariableList list = d_assignedWatchManager.get(listRef);
    Debug("mcsat::uf") << "UFPlugin::newUninterpretedFunction(" << f_app << "): new list " << list << std::endl;

    // Watch the first variable
    d_assignedWatchManager.watch(vars[0], listRef);

    // Mark as assigned
    if (d_trail.hasValue(vars[0])) {
      markChildrenAssigned(f_app);
      Assert(!d_trail.hasValue(f_app));
    }
  } else {
    markChildrenAssigned(f_app);
    Assert(!d_trail.hasValue(f_app));
  }
  
  // Stats
  ++ d_stats.applications;
}

void UFPlugin::markChildrenAssigned(Variable var) {
  Assert(!hasChildrenAssigned(var));
  
  Debug("mcsat::uf") << "UFPlugin::markChildrenAssigned(" << var << ")" << std::endl;
  
  TNode node = var.getNode();
  
  // Evaluate the application
  NodeBuilder<> nb(node.getKind());
  if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
    nb << node.getOperator();
  }
  for (unsigned i = 0; i < node.getNumChildren(); ++ i) {
    if (node[i].isConst()) {
      nb << node[i];
    } else {
      Assert(VariableDatabase::getCurrentDB()->hasVariable(node[i]));
      Variable child = VariableDatabase::getCurrentDB()->getVariable(node[i]);
      Assert(d_trail.hasValue(child));
      nb << d_trail.value(child);
    }
  }
  Node eval = nb;
  
  // Add to the map
  d_appEvaluation.insert(var, eval);
}

bool UFPlugin::hasChildrenAssigned(Variable fApp) const {
  evaluation_map::const_iterator find = d_appEvaluation.find(fApp);
  return find != d_appEvaluation.end();
}

void UFPlugin::markAppAssigned(Variable fApp) {
  Assert(hasChildrenAssigned(fApp));
  Assert(d_trail.hasValue(fApp));
  
  Debug("mcsat::uf") << "UFPlugin::markAppAssigned(" << fApp << ")" << std::endl;

  // Get the evaluation
  TNode fAppEval = d_appEvaluation[fApp];
  
  // Check if there is a value already 
  value_map::const_iterator find = d_valueMap.find(fAppEval);
  if (find != d_valueMap.end()) {
    if ((*find).second.value != d_trail.value(fApp)) {
      // Ackermann
      Debug("mcsat::uf") << "UFPlugin::markAppAssigned(" << fApp << "): conflict with " << (*find).second.app << std::endl;
      d_conflicts.push_back(std::pair<Variable, Variable>(fApp, (*find).second.app));
    }
  } else {
    // No value, add it
    d_valueMap[fAppEval] = value_info(fApp, d_trail.value(fApp));
  }
}

void UFPlugin::propagate(SolverTrail::PropagationToken& out) {
  Debug("mcsat::uf") << "UFPlugin::propagate()" << std::endl;

  // If we're not watching anything, we just ignore
  if (d_assignedWatchManager.size() == 0) {
    return;
  }
  
  unsigned i = d_trailHead;
  for (; i < d_trail.size() && d_trail.consistent(); ++ i) {
    
    Variable var = d_trail[i].var;

    Debug("mcsat::uf") << "UFPlugin::propagate(): " << var << std::endl;

    // Go through all the variable lists (constraints) where we're watching var
    AssignedWatchManager::remove_iterator w = d_assignedWatchManager.begin(var);
    while (d_trail.consistent() && !w.done()) {

      // Get the current list where var appears
      VariableListReference variableListRef = *w;
      VariableList variableList = d_assignedWatchManager.get(variableListRef);
      Debug("mcsat::uf") << "UFPlugin::propagate(): watchlist  " << variableList << " assigned due to " << var << std::endl;

      // Try to find a new watch
      bool watchFound = false;
      for (unsigned j = 1; j < variableList.size(); j++) {
	if (!d_trail.hasValue(variableList[j])) {
	  // Put the new watch in place
          variableList.swap(0, j);
	  d_assignedWatchManager.watch(variableList[0], variableListRef);
          w.next_and_remove();
          // We found a watch
          watchFound = true;
          break;
        }
      }

      Debug("mcsat::uf") << "UFPlugin::propagate(): new watch " << (watchFound ? "found" : "not found") << std::endl;

      if (!watchFound) {
	// We did not find a new watch so vars[1], ..., vars[n] are assigned
	Variable app = d_assignedWatchManager.getConstraint(variableListRef);
        markChildrenAssigned(app);
	// If it is also assigned to a value
	if (d_trail.hasValue(app)) {
	  markAppAssigned(app);
	}	
	// Keep the watch, and continue
        w.next_and_keep();
      }
    }
    
    // If it's an application with all assigned
    if (hasChildrenAssigned(var)) {
      markAppAssigned(var);
    }    
  }

  // Remember where we stopped
  d_trailHead = i;

  // Expand all the conflicts with ackerman
  for (unsigned i = 0; i < d_conflicts.size(); ++ i) {
    std::set<Variable> varsToBump;
    d_ackermannRule.apply(d_conflicts[i].first, d_conflicts[i].second, out, varsToBump);

    // Bump the variables
    std::set<Variable>::const_iterator it = varsToBump.begin();
    std::set<Variable>::const_iterator it_end = varsToBump.end();
    for (; it != it_end; ++ it) {
      d_request.bump(*it, options::mcsat_uf_bump());
    }
  }

  d_conflicts.clear();  
}

void UFPlugin::notifyBackjump(const std::vector<Variable>& vars) {
}

void UFPlugin::gcMark(std::set<Variable>& varsToKeep, std::set<CRef>& clausesToKeep) {
}

void UFPlugin::gcRelocate(const VariableGCInfo& vReloc, const ClauseRelocationInfo& cReloc) {
}



