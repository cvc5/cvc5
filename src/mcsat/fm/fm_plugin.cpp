#include "mcsat/fm/fm_plugin.h"
#include "options/mcsat_options.h"

using namespace CVC4;
using namespace mcsat;
using namespace fm;
using namespace util;

FMPlugin::NewVariableNotify::NewVariableNotify(FMPlugin& plugin)
: INewVariableNotify(false)
, d_plugin(plugin)
{
}

void FMPlugin::NewVariableNotify::newVariable(Variable var) {
  // Register arithmetic constraints
  TNode varNode = var.getNode();
  switch(varNode.getKind()) {
  case kind::LT:
  case kind::LEQ:
  case kind::GT:
  case kind::GEQ:
    // Arithmetic constraints
    d_plugin.newConstraint(var);
    break;
  case kind::EQUAL:
    // TODO: Only if both sides are arithmetic
    d_plugin.newConstraint(var);
    break;
  default:
    // Ignore
    break;
  }
}

struct ConstraintDiscriminator : public IConstraintDiscriminator {
  const SolverTrail& trail;
  const std::vector<LinearConstraint>& constraints;

  bool size;
  bool level;
public:

  ConstraintDiscriminator(const SolverTrail& trail, const std::vector<LinearConstraint>& constraints, bool size, bool level)
  : trail(trail)
  , constraints(constraints)
  , size(size)
  , level(level)
  {}

  bool better(Variable c1, Variable c2) {

    if (level) {
      unsigned l1 = trail.decisionLevel(c1);
      unsigned l2 = trail.decisionLevel(c2);
      if (l1 != l2) {
        return l1 < l2;
      }
    }

    if (size) {
      return constraints[c1.index()].size() < constraints[c2.index()].size();
    }

    return false;
  }
};

FMPlugin::FMPlugin(ClauseDatabase& database, const SolverTrail& trail, SolverPluginRequest& request, StatisticsRegistry* registry)
: SolverPlugin(database, trail, request, registry)
, d_stats(registry)
, d_newVariableNotify(*this)
, d_intTypeIndex(VariableDatabase::getCurrentDB()->getTypeIndex(NodeManager::currentNM()->integerType()))
, d_realTypeIndex(VariableDatabase::getCurrentDB()->getTypeIndex(NodeManager::currentNM()->realType()))
, d_boolTypeIndex(VariableDatabase::getCurrentDB()->getTypeIndex(NodeManager::currentNM()->booleanType()))
, d_fixedVariables(trail.getSearchContext())
, d_fixedVariablesIndex(trail.getSearchContext(), 0)
, d_fixedVariablesDecided(trail.getSearchContext(), 0)
, d_constraintsCount(0)
, d_constraintsSizeSum(0)
, d_trailHead(trail.getSearchContext(), 0)
, d_bounds(trail.getSearchContext(), registry)
, d_fmRule(database, trail, registry)
, d_fmRuleDiseq(database, trail, registry)
, d_splitRule(database, trail, registry)
, d_constraintDiscriminator(new ConstraintDiscriminator(d_trail, d_constraints, options::mcsat_fm_discriminate_size(), options::mcsat_fm_discriminate_level()))
, d_reasonProvider(*this, trail.getSearchContext())
{
  Debug("mcsat::fm") << "FMPlugin::FMPlugin()" << std::endl;

  // We decide values of variables and can detect conflicts
  addFeature(CAN_PROPAGATE);
  addFeature(CAN_DECIDE_VALUES);

  // Notifications we need
  addNotification(NOTIFY_BACKJUMP);

  // Add the listener
  VariableDatabase::getCurrentDB()->addNewVariableListener(&d_newVariableNotify);

  // Add the comparator for bounds
  if (options::mcsat_fm_discriminate()) {
    d_bounds.setDiscriminator(d_constraintDiscriminator);
  }
}

FMPlugin::~FMPlugin() {
  delete d_constraintDiscriminator;
}

std::string FMPlugin::toString() const  {
  return "Fourier-Motzkin Elimination (Model-Based)";
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

void FMPlugin::newConstraint(Variable constraint) {
  Debug("mcsat::fm") << "FMPlugin::newConstraint(" << constraint << ")" << std::endl;
  Assert(!isLinearConstraint(constraint), "Already registered");

  // The linear constraint we're creating 
  LinearConstraint linearConstraint;

  // Parse the coefficients into the constraint
  bool linear = LinearConstraint::parse(Literal(constraint, false), linearConstraint);
  if (!linear) {
    // The plugin doesn't handle non-linear constraints
    Debug("mcsat::fm") << "FMPlugin::newConstraint(" << constraint << "): non-linear" << std::endl;
    return;
  }

  Debug("mcsat::fm") << "FMPlugin::newConstraint(" << constraint << "): " << linearConstraint << std::endl;

  // Get the variables of the constraint
  std::vector<Variable> vars;
  linearConstraint.getVariables(vars);
  Assert(vars.size() > 0);

  // Sort the variables by trail assignment index (if any)
  var_assign_compare cmp(d_trail);
  std::sort(vars.begin(), vars.end(), cmp);

  // Add the variable list to the watch manager and watch the first two constraints
  VariableListReference listRef = d_assignedWatchManager.newListToWatch(vars, constraint);
  VariableList list = d_assignedWatchManager.get(listRef);
  Debug("mcsat::fm") << "FMPlugin::newConstraint(" << constraint << "): new list " << list << std::endl;

  d_assignedWatchManager.watch(vars[0], listRef);
  if (vars.size() > 1) {
    d_assignedWatchManager.watch(vars[1], listRef);
  }

  if (constraint.index() >= d_constraints.size()) {
    d_constraints.resize(constraint.index() + 1);
  }
  
  // Remember the constraint
  d_constraintsCount ++;
  d_constraintsSizeSum += linearConstraint.size();
  d_constraints[constraint.index()].swap(linearConstraint);
  
  // Resize the unit info if necessary 
  if (constraint.index() >= d_unitInfo.size()) {
    d_unitInfo.resize(constraint.index() + 1);
  }
  
  // Check if anything to do immediately
  if (!d_trail.hasValue(vars[0])) {
    if (vars.size() == 1 || d_trail.hasValue(vars[1])) {
      // Single variable is unassigned
      if (vars[0] != d_lastDecidedAndUnprocessed) {
        d_unitInfo[constraint.index()].setUnit(vars[0]);
      }
      Debug("mcsat::fm") << "FMPlugin::newConstraint(" << constraint << "): unit " << std::endl;
    }
  } else {
    // All variables are unassigned
    if (vars[0] != d_lastDecidedAndUnprocessed) {
      d_unitInfo[constraint.index()].setFullyAssigned();
    } else {
      d_unitInfo[constraint.index()].setUnit(vars[0]);
    }
    Debug("mcsat::fm") << "FMPlugin::newConstraint(" << constraint << "): all assigned " << std::endl;
  }
}

void FMPlugin::propagate(SolverTrail::PropagationToken& out) {
  Debug("mcsat::fm") << "FMPlugin::propagate()" << std::endl;

  unsigned i = d_trailHead;
  for (; i < d_trail.size() && d_trail.consistent(); ++ i) {
    Variable var = d_trail[i].var;

    if (isArithmeticVariable(var)) {

      Debug("mcsat::fm") << "FMPlugin::propagate(): " << var << " assigned" << std::endl;
      
      if (var == d_lastDecidedAndUnprocessed) {
        // We've processed our last decision
        d_lastDecidedAndUnprocessed = Variable::null;
      }

      // Go through all the variable lists (constraints) where we're watching var
      AssignedWatchManager::remove_iterator w = d_assignedWatchManager.begin(var);
      while (d_trail.consistent() && !w.done()) {

        // Get the current list where var appears
        VariableListReference variableListRef = *w;
        VariableList variableList = d_assignedWatchManager.get(variableListRef);
        Debug("mcsat::fm") << "FMPlugin::propagate(): watchlist  " << variableList << " assigned" << std::endl;

        // More than one vars, put the just assigned var to position [1]
        if (variableList.size() > 1 && variableList[0] == var) {
          variableList.swap(0, 1);
        }

        // Try to find a new watch
        bool watchFound = false;
        for (unsigned j = 2; j < variableList.size(); j++) {
          if (!d_trail.hasValue(variableList[j])) {
            // Put the new watch in place
            variableList.swap(1, j);
            d_assignedWatchManager.watch(variableList[1], variableListRef);
            w.next_and_remove();
            // We found a watch
            watchFound = true;
            break;
          }
        }

        Debug("mcsat::fm") << "FMPlugin::propagate(): new watch " << (watchFound ? "found" : "not found") << std::endl;

        if (!watchFound) {
          // We did not find a new watch so vars[1], ..., vars[n] are assigned, except maybe vars[0]
          if (d_trail.hasValue(variableList[0])) {
            // Even the first one is assigned, so we have a semantic propagation
            Variable constraintVar = d_assignedWatchManager.getConstraint(variableListRef);
            d_unitInfo[constraintVar.index()].setFullyAssigned();
            if (!d_trail.hasValue(constraintVar)) {
              unsigned valueLevel;
              const LinearConstraint& constraint = getLinearConstraint(constraintVar);
              bool value = constraint.evaluate(d_trail, valueLevel);
              out(Literal(constraintVar, !value), valueLevel);
              ++ d_stats.propagationS;
            } else {
              Assert(getLinearConstraint(constraintVar).evaluate(d_trail) == d_trail.isTrue(constraintVar));
            }
          } else {
            // The first one is not assigned, so we have a new unit constraint
            Variable constraintVar = d_assignedWatchManager.getConstraint(variableListRef);
            d_unitInfo[constraintVar.index()].setUnit(variableList[0]);
	    // Process the unit constraint
	    processUnitConstraint(constraintVar, out);
	  }
          // Keep the watch, and continue
          w.next_and_keep();
        }
      }
    } else if (isLinearConstraint(var)) {
      Debug("mcsat::fm") << "FMPlugin::propagate(): processing " << var << " -> " << d_trail.value(var) << std::endl;
      // If the constraint is unit we propagate a new bound
      if (isUnitConstraint(var)) {
        processUnitConstraint(var, out);
      } else {
	Assert(!isFullyAssigned(var) || getLinearConstraint(var).evaluate(d_trail) == d_trail.isTrue(var));
      }
    }
  }

  // Remember where we stopped
  d_trailHead = i;

  // Process any conflicts
  if (d_bounds.inConflict()) {
    processConflicts(out);
  } 
}

bool FMPlugin::SimpleReasonProvider::add(Literal propagation, Literal reason, Variable x) {
  if (d_reasons.find(propagation) == d_reasons.end()) {
    d_reasons.insert(propagation, PropInfo(reason, x));
    return true;
  } else {
    return false;
  }
}

CRef FMPlugin::SimpleReasonProvider::explain(Literal l, SolverTrail::PropagationToken& out) {
  reason_map::const_iterator find = d_reasons.find(l);
  Assert(find != d_reasons.end());
  // Explaining R, L are true in the model, therefore R, ~L => False, or R, ~False => L
  d_plugin.d_fmRule.start(~l);
  d_plugin.d_fmRule.resolve(find->second.x, find->second.reason);
  if (options::mcsat_fm_cascade()) {
    std::set<Variable> variables;
    d_plugin.minimizeResolvent(variables);
  }
  CRef explanation = d_plugin.d_fmRule.finish(out);
  return explanation;
}

void FMPlugin::propagateDeduction(Literal propagation, Literal reason, Variable x, SolverTrail::PropagationToken& out) {
  if (d_reasonProvider.add(propagation, reason, x)) {
    out(propagation, &d_reasonProvider);
    ++ d_stats.propagationD;
  }
}

bool FMPlugin::isUnitConstraint(Variable constraint) const {
  return d_unitInfo[constraint.index()].isUnit();
}

bool FMPlugin::isFullyAssigned(Variable constraint) const {
  return d_unitInfo[constraint.index()].isFullyAssigned();
}

Literal FMPlugin::tryBounding(const BoundingInfo& bounding, Variable var) const {

  if (bounding.isLowerBound()) {
    if (d_bounds.hasUpperBound(var)) {
      const BoundInfo& uBound = d_bounds.getUpperBoundInfo(var);
      BoundInfo lBound(bounding.value, bounding.isStrict());
      if (BoundInfo::inConflict(lBound, uBound)) {
        return uBound.reason;
      }
    }
  }

  if (bounding.isUpperBound()) {
    if (d_bounds.hasLowerBound(var)) {
      const BoundInfo& lBound = d_bounds.getLowerBoundInfo(var);
      BoundInfo uBound(bounding.value, bounding.isStrict());
      if (BoundInfo::inConflict(lBound, uBound)) {
        return lBound.reason;
      }
    }
  }

  return Literal();
}

void FMPlugin::processUnitConstraint(Variable constraint, SolverTrail::PropagationToken& out) {
  Debug("mcsat::fm") << "FMPlugin::processUnitConstraint(" << constraint << ")" << std::endl;
  
  Assert(isLinearConstraint(constraint));
  Assert(isUnitConstraint(constraint));

  // Get the constraint
  const LinearConstraint& c = getLinearConstraint(constraint);

  // Variable to bound
  Variable var = d_unitInfo[constraint.index()].getUnitVar();
  Assert(!var.isNull());
  Assert(!d_trail.hasValue(var));

  Debug("mcsat::fm") << "FMPlugin::processUnitConstraint(): " << c << " with value " << d_trail.value(constraint) << " unit for " << var << std::endl;

  // If the constraint has a value then try to assert it to the model 
  if (d_trail.hasValue(constraint)) {

    // Bound the variable with the constraint  
    BoundingInfo boundingInfo = c.bound(var, d_trail);

    // If the constraint is negated, negate the bound
    Literal constraintLiteral(constraint, d_trail.isFalse(constraint));
    if (d_trail.isFalse(constraint)) {
      boundingInfo.negate();
    }

    // Data for the bound
    BoundInfo bound(boundingInfo.value, boundingInfo.isStrict(), constraintLiteral);

    // Does this bound fix the value of the variable
    CDBoundsModel::update_info u1;
    if (boundingInfo.isLowerBound()) {
      u1 = d_bounds.updateLowerBound(var, bound);
    }
    CDBoundsModel::update_info u2;
    if (boundingInfo.isUpperBound()) {
      u2 = d_bounds.updateUpperBound(var, bound);
    }
    if (boundingInfo.kind == kind::DISTINCT) {
      d_bounds.addDisequality(var, DisequalInfo(boundingInfo.value, constraint));
    }

    // If the variable is fixed, remember it
    if (u1.fixed || u2.fixed) {
      d_fixedVariables.push_back(var);
    }  
  } else if (options::mcsat_fm_deductive_propagate()) {

    // Bound the variable with the constraint  
    BoundingInfo boundingInfo = c.bound(var, d_trail);

    // Try the positive bounding
    Literal conflict = tryBounding(boundingInfo, var);
    if (!conflict.isNull()) {
      Literal propagation(constraint, true);
      propagateDeduction(propagation, conflict, var, out);
      return;
    }

    // Try the negated bounding
    boundingInfo.negate();
    conflict = tryBounding(boundingInfo, var);
    if (!conflict.isNull()) {
      Literal propagation(constraint, false);
      propagateDeduction(propagation, conflict, var, out);
      return;
    }

  }
}

void FMPlugin::bumpVariables(const LinearConstraint& c) {
  LinearConstraint::const_iterator it = c.begin();
  LinearConstraint::const_iterator it_end = c.end();
  for (; it != it_end; ++ it) {
    if (!it->first.isNull()) {
      d_request.bump(it->first, options::mcsat_fm_bump());
    }
  }
}

void FMPlugin::bumpVariables(const std::set<Variable>& vars) {
  std::set<Variable>::const_iterator it = vars.begin();
  std::set<Variable>::const_iterator it_end = vars.end();
  for (; it != it_end; ++ it) {
    d_request.bump(*it, options::mcsat_fm_bump());
  }
}

void FMPlugin::bumpVariables(const std::vector<Variable>& vars) {
  std::vector<Variable>::const_iterator it = vars.begin();
  std::vector<Variable>::const_iterator it_end = vars.end();
  for (; it != it_end; ++ it) {
    d_request.bump(*it, options::mcsat_fm_bump());
  }
}



void FMPlugin::minimizeResolvent(std::set<Variable>& vars) {

  // Resolve top variable as long as it is still in conflict
  do {

    // Get the current constraint and see if it breaks any current boudns
    const LinearConstraint& current = d_fmRule.getCurrentResolvent();

    // Get the top variable
    Variable var = current.getTopVariable(d_trail);

    // No variable, awesome
    if (var.isNull()) {
      break;
    }

    // Bound the variable with the constraint
    BoundingInfo boundingInfo = current.bound(var, d_trail);

    // Try to bound
    Literal conflictLiteral = tryBounding(boundingInfo, var);

    // If there
    if (!conflictLiteral.isNull()) {
      // We got a bound conflict we can resolve further
      Assert(d_trail.isTrue(conflictLiteral));
      d_fmRule.resolve(var, conflictLiteral);
      getLinearConstraint(conflictLiteral.getVariable()).getVariables(vars);
    } else {
      // No conflict, break
      break;
    }

  } while (true);
  
  // Resolve all the equalities
  do {
    
    if (!options::mcsat_fm_equality_resolution()) {
      break;
    }
 
    // Get the current constraint and see if it breaks any current boudns
    const LinearConstraint& current = d_fmRule.getCurrentResolvent();
    
    // Find the top fixed variable we can replace
    Variable topVar;
    unsigned topLevel = 0;
    Literal topReason;
    LinearConstraint::const_iterator it = current.begin();
    LinearConstraint::const_iterator it_end = current.end();
    for (; it != it_end; ++ it) {
      Variable currentVar = it->first;
      if (currentVar.isNull()) continue;
      unsigned currentLevel = d_trail.decisionLevel(currentVar);
      if (currentLevel <= topLevel) continue;
      if (!d_bounds.isFixed(currentVar)) continue;
      Literal lReason = d_bounds.getLowerBoundInfo(currentVar).reason;
      Literal uReason = d_bounds.getUpperBoundInfo(currentVar).reason;
      if (lReason != uReason) {
	continue;
      }      
      // We have an equality for sure
      topVar = currentVar;
      topLevel = currentLevel;
      topReason = lReason;
    }
    
    if (!topVar.isNull()) {
      Debug("mcsat::fm::fixed") << "FMPlugin::minimizeResolvent(): resolving " << topReason << std::endl;
      d_fmRule.resolve(topVar, topReason);
      getLinearConstraint(topReason.getVariable()).getVariables(vars);
    } else {
      break;
    }
    
  } while (true);
}

void FMPlugin::processConflicts(SolverTrail::PropagationToken& out) {
  std::set<Variable> variablesInConflict;
  d_bounds.getVariablesInConflict(variablesInConflict);

  std::set<Variable>::const_iterator it = variablesInConflict.begin();
  std::set<Variable>::const_iterator it_end = variablesInConflict.end();
  for (; it != it_end; ++ it) {

    ++ d_stats.conflicts;

    Variable var = *it;

    const BoundInfo& lowerBound = d_bounds.getLowerBoundInfo(var);
    const BoundInfo& upperBound = d_bounds.getUpperBoundInfo(var);

    std::set<Variable> varsToBump;
    
    CRef conflict;
    if (BoundInfo::inConflict(lowerBound, upperBound)) {
      // Clash of bounds
      Variable lowerBoundVariable = lowerBound.reason.getVariable();
      Variable upperBoundVariable = upperBound.reason.getVariable();

      // Bump the variables involved
      getLinearConstraint(lowerBoundVariable).getVariables(varsToBump);
      getLinearConstraint(upperBoundVariable).getVariables(varsToBump);

      // Do the initial resolution 
      d_fmRule.start(lowerBound.reason);
      d_fmRule.resolve(var, upperBound.reason);

      if (options::mcsat_fm_cascade()) {
        minimizeResolvent(varsToBump);
      }
      
      // Finish up
      conflict = d_fmRule.finish(out);
    } else {
      // Bounds clash with a disequality
      Variable lowerBoundVariable = lowerBound.reason.getVariable();
      Variable upperBoundVariable = upperBound.reason.getVariable();

      Assert (!lowerBound.strict && !upperBound.strict && lowerBound.value == upperBound.value);
      const DisequalInfo& disequal = d_bounds.getDisequalInfo(var, lowerBound.value);
      Assert(d_trail.isFalse(disequal.reason));
      Literal disequalityLiteral(disequal.reason, true);

      // Bump the variables
      getLinearConstraint(lowerBoundVariable).getVariables(varsToBump);
      getLinearConstraint(upperBoundVariable).getVariables(varsToBump);
      getLinearConstraint(disequal.reason).getVariables(varsToBump);
 
      conflict = d_fmRuleDiseq.resolveDisequality(var, lowerBound.reason, upperBound.reason, disequalityLiteral, out);
    }
    
    // Actually bump the variables
    bumpVariables(varsToBump);
  }
}

void FMPlugin::decide(SolverTrail::DecisionToken& out, Variable var) {
  Debug("mcsat::fm") << "FMPlugin::decide(): level " << d_trail.decisionLevel() << std::endl;
  Assert(d_trailHead == d_trail.size());

  // Do any fixed variables first
  if (options::mcsat_fm_decide_fixed()) {
    for (; d_fixedVariablesIndex < d_fixedVariables.size(); d_fixedVariablesIndex = d_fixedVariablesIndex + 1) {
      Variable var = d_fixedVariables[d_fixedVariablesIndex];
      if (!d_trail.hasValue(var)) {
        Rational value = d_bounds.pick(var, false);
        Debug("mcsat::fm::decide") << "FMPlugin::decide(): " << var << " fixed at " << d_trail.decisionLevel() << std::endl;
        out(var, NodeManager::currentNM()->mkConst(value), true, true);
        d_lastDecidedAndUnprocessed = var;
        d_fixedVariablesDecided = d_fixedVariablesDecided + 1;
        ++ d_stats.decisions_f;
	return;
      }
    }
  }
  
  if (isArithmeticVariable(var)) {
    Rational value = d_bounds.pick(var, true);
    out(var, NodeManager::currentNM()->mkConst(value), true);
    d_lastDecidedAndUnprocessed = var;
    ++ d_stats.decisions;
    return;
  }
}

void FMPlugin::notifyBackjump(const std::vector<Variable>& vars) {

  Debug("mcsat::fm") << "FMPlugin::notifyBackjump(): " << d_trail.decisionLevel() << std::endl;

  for (unsigned i = 0; i < vars.size(); ++ i) {
    if (isArithmeticVariable(vars[i])) {

      Debug("mcsat::fm") << "FMPlugin::notifyBackjump(): " << vars[i] << std::endl;

      // If we didn't process this assignment yet, we should skip it
      if (d_lastDecidedAndUnprocessed == vars[i]) {
        Debug("mcsat::fm") << "FMPlugin::notifyBackjump(): " << vars[i] << ": skipping, it's the last decision" << std::endl;
        d_lastDecidedAndUnprocessed = Variable::null;
        continue;
      }

      // Go through the watch and mark the constraints
      // UNASSIGNED_UNKNOWN -> UNASSIGNED_UNKNOWN
      // UNASSIGNED_UNIT    -> UNASSIGNED_UNKNOWN
      // UNASSIGNED_NONE    -> UNASSIGNED_UNIT
      AssignedWatchManager::remove_iterator w = d_assignedWatchManager.begin(vars[i]);
      while (!w.done()) {
        // Get the current list where var appears
        Variable constraintVar = d_assignedWatchManager.getConstraint(*w);
        unit_info& ui = d_unitInfo[constraintVar.index()];
	if (ui.isFullyAssigned()) {
          Debug("mcsat::fm") << "FMPlugin::notifyBackjump(): " << vars[i] << ": " << constraintVar << " -> unit" << std::endl;
	  ui.setUnit(vars[i]);
	} else if (ui.isUnit()) {
          Debug("mcsat::fm") << "FMPlugin::notifyBackjump(): " << vars[i] << ": " << constraintVar << " -> none" << std::endl;
	  ui.unsetUnit();
	} else {
          Debug("mcsat::fm") << "FMPlugin::notifyBackjump(): " << vars[i] << ": " << constraintVar << " none -> none" << std::endl;
	}
        w.next_and_keep();
      }
    }
  }
}

struct lemma_cmp {
  bool operator () (const CRef& c1, const CRef c2) {
    Clause& clause1 = c1.getClause();
    Clause& clause2 = c2.getClause();
    if (clause1.size() == clause2.size()) {
      // Random for now
      return c1 < c2;
    } else {
      return clause1.size() < clause2.size();
    }
  }
};

void FMPlugin::gcMark(std::set<Variable>& varsToKeep, std::set<CRef>& clausesToKeep) {
  // Noting so for
}

void FMPlugin::gcRelocate(const VariableGCInfo& vReloc, const ClauseRelocationInfo& cReloc) {

  // Type of constraints 
  size_t boolType = VariableDatabase::getCurrentDB()->getTypeIndex(NodeManager::currentNM()->booleanType());
  
  // Go throuth deleted constraints 
  if (vReloc.size(boolType) > 0) {
    VariableGCInfo::const_iterator it = vReloc.begin(boolType);
    VariableGCInfo::const_iterator it_end = vReloc.end(boolType);
    for (; it != it_end; ++ it) {
      if (isLinearConstraint(*it)) {
	Variable c = *it;
	// Remove info
	d_constraintsCount --;
	d_constraintsSizeSum -= d_constraints[c.index()].size();
        // Remove from map: variables -> constraints
        d_constraints[c.index()].clear();
        // Set status to unknwon
        d_unitInfo[c.index()].unsetUnit();
      }
    }
  }

  // Relocate the watch manager
  d_assignedWatchManager.gcRelocate(vReloc);
}

void FMPlugin::outputStatusHeader(std::ostream& out) const {	
  out 
    << std::setw(10) << "Constr"
    << std::setw(10) << "Avg sz"
    << std::setw(10) << "Fixed";
}

void FMPlugin::outputStatusLine(std::ostream& out) const {
  out 
    << std::setw(10) << d_constraintsCount
    << std::setw(10) << std::setprecision(4) << (double) d_constraintsSizeSum / d_constraintsCount
    << std::setw(10) << d_fixedVariables.size();  
}

