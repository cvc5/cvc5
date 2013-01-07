#include "mcsat/fm/bounds_model.h"
#include "mcsat/options.h"

using namespace CVC4;
using namespace mcsat;
using namespace fm;

CDBoundsModel::CDBoundsModel(context::Context* context)
: context::ContextNotifyObj(context)
, d_boundTrailSize(context, 0)
, d_disequalTrailSize(context, 0)
, d_constraintCMP(0)
{
}

void CDBoundsModel::contextNotifyPop() {
  
  // Go back and undo the updates 
  for (int i = d_boundTrail.size() - 1; i >= (int) d_boundTrailSize; -- i) {
    const UndoBoundInfo& undo = d_boundTrailUndo[i];
    if (undo.isLower) {
      bound_map::iterator find = d_lowerBounds.find(undo.var);
      if (undo.prev == null_bound_index) {
	d_lowerBounds.erase(find);
      } else {
	find->second = undo.prev;
      }
    } else {
      bound_map::iterator find = d_upperBounds.find(undo.var);
      if (undo.prev == null_bound_index) {
	d_upperBounds.erase(find);
      } else {
	find->second = undo.prev;
      }
    }
  }
  
  // Resize the trail to size
  d_boundTrail.resize(d_boundTrailSize);
  d_boundTrailUndo.resize(d_boundTrailSize);

  // Go back and undo the updates
  for (int i = d_disequalTrail.size() - 1; i >= (int) d_disequalTrailSize; -- i) {
    const UndoDisequalInfo& undo = d_disequalTrailUndo[i];
    disequal_map::iterator find = d_disequalValues.find(undo.var);
    if (undo.prev == null_bound_index) {
      d_disequalValues.erase(find);
    } else {
      find->second = undo.prev;
    }
  }

  // Resize the trail to size
  d_disequalTrail.resize(d_disequalTrailSize);
  d_disequalTrailUndo.resize(d_disequalTrailSize);

  // Clear any conflicts 
  d_variablesInConflict.clear();
}

void CDBoundsModel::addDisequality(Variable var, const DisequalInfo& info) {

  // If the value is outside of the feasible range, we can ignore it
  bool onlyOption = false;
  if (inRange(var, info.value, onlyOption)) {

    Debug("mcsat::fm") << "CDBoundsModel::addDiseq(" << var << ", " << info << ")" << std::endl;

    // Add the new info to the trail
    DisequalInfoIndex index = d_disequalTrail.size();
    d_disequalTrail.push_back(info);

    disequal_map::iterator find = d_disequalValues.find(var);
    if (find == d_disequalValues.end()) {
      d_disequalTrailUndo.push_back(UndoDisequalInfo(var, null_diseqal_index));
      d_disequalValues[var] = index;
    } else {
      d_disequalTrailUndo.push_back(UndoDisequalInfo(var, find->second));
      find->second = index;
    }

    // Update the trail size
    d_disequalTrailSize = d_disequalTrail.size();

    if (onlyOption) {
      // Conflict
      d_variablesInConflict.insert(var);
      Debug("mcsat::fm") << "CDBoundsModel::addDiseq(" << var << ", " << info << "): bound and diseq conflict" << std::endl;
    }
  }
}

bool CDBoundsModel::improvesLowerBound(Variable var, const BoundInfo& lBound) const {
  // If no lower bound, done
  if (!hasLowerBound(var)) return true;

  // 1: improves, 0: same, -1 doesn't improve
  int cmp = lBound.improvesLowerBound(getLowerBoundInfo(var));
  if (cmp > 0) {
    // Definitively better
    return true;
  } else if (cmp < 0) {
    // Definitively worse
    return false;
  } else {
    // Same, compare
    if (d_constraintCMP) {
      return d_constraintCMP->better(lBound.reason.getVariable(), getLowerBoundInfo(var).reason.getVariable());
    } else {
      return false;
    }
  }
}

bool CDBoundsModel::improvesUpperBound(Variable var, const BoundInfo& uBound) const {
  // If no lower bound, done
  if (!hasUpperBound(var)) return true;

  // 1: improves, 0: same, -1 doesn't improve
  int cmp = uBound.improvesUpperBound(getUpperBoundInfo(var));
  if (cmp > 0) {
    // Definitively better
    return true;
  } else if (cmp < 0) {
    // Definitively worse
    return false;
  } else {
    // Same, compare
    if (d_constraintCMP) {
      return d_constraintCMP->better(uBound.reason.getVariable(), getUpperBoundInfo(var).reason.getVariable());
    } else {
      return false;
    }
  }
}

CDBoundsModel::update_info CDBoundsModel::updateLowerBound(Variable var, const BoundInfo& lBound) {

  Assert(!lBound.reason.isNull());

  update_info result;

  // Update if better than the current one
  if (improvesLowerBound(var, lBound)) {
    
    Debug("mcsat::fm") << "CDBoundsModel::updateLowerBound(" << var << ", " << lBound << ")" << std::endl;
    result.updated = true;

    // Add the new info to the trail
    BoundInfoIndex index = d_boundTrail.size();
    d_boundTrail.push_back(lBound);
  
    // Update the bound and prev info
    bound_map::iterator find = d_lowerBounds.find(var);
    if (find == d_lowerBounds.end()) {
      // New bound
      d_boundTrailUndo.push_back(UndoBoundInfo(var, null_bound_index, true));
      d_lowerBounds[var] = index;
    } else {
      d_boundTrailUndo.push_back(UndoBoundInfo(var, find->second, true));
      find->second = index;
    }
  
    // Update trail size
    d_boundTrailSize = d_boundTrail.size();

    // Mark if new bound in conflict
    if (hasUpperBound(var)) {
      const BoundInfo& uBound = getUpperBoundInfo(var);
      // Bounds in conflict
      if (BoundInfo::inConflict(lBound, uBound)) {
        d_variablesInConflict.insert(var);
        Debug("mcsat::fm") << "CDBoundsModel::updateLowerBound(" << var << ", " << lBound << "): bound conflict" << std::endl;
      }
      // Bounds imply a value that is in the disequal list
      else if (!lBound.strict && !uBound.strict && lBound.value == uBound.value) {
        if (isDisequal(var, lBound.value)) {
          d_variablesInConflict.insert(var);
          Debug("mcsat::fm") << "CDBoundsModel::updateLowerBound(" << var << ", " << lBound << "): bound and diseq conflict" << std::endl;
        }
        // Value for var is now fixed
        result.fixed = true;
      }
    }
  }

  return result;
}

CDBoundsModel::update_info CDBoundsModel::updateUpperBound(Variable var, const BoundInfo& uBound) {

  Assert(!uBound.reason.isNull());

  update_info result;

  if (improvesUpperBound(var, uBound)) {

    Debug("mcsat::fm") << "CDBoundsModel::updateUpperBound(" << var << ", " << uBound << ")" << std::endl;
    result.updated = true;

    // Add the new info to the trail
    BoundInfoIndex index = d_boundTrail.size();
    d_boundTrail.push_back(uBound);
  
    // Update the bound and prev info
    bound_map::iterator find = d_upperBounds.find(var);
    if (find == d_upperBounds.end()) {
      // New bound
      d_boundTrailUndo.push_back(UndoBoundInfo(var, null_bound_index, false));
      d_upperBounds[var] = index;  
    } else {
      d_boundTrailUndo.push_back(UndoBoundInfo(var, find->second, false));
      find->second = index;
    }
  
    // Update trail size
    d_boundTrailSize = d_boundTrail.size();

    // Mark if new bound in conflict
    if (hasLowerBound(var)) {
      const BoundInfo& lBound = getLowerBoundInfo(var);
      // Bounds in conflictr
      if (BoundInfo::inConflict(lBound, uBound)) {
        Debug("mcsat::fm") << "CDBoundsModel::updateUpperBound(" << var << ", " << uBound << "): bound conflict" << std::endl;
        d_variablesInConflict.insert(var);
      }
      // Bounds imply a value that is in the disequal list
      else if (!lBound.strict && !uBound.strict && lBound.value == uBound.value) {
        if (isDisequal(var, lBound.value)) {
          d_variablesInConflict.insert(var);
          Debug("mcsat::fm") << "CDBoundsModel::updateUpperBound(" << var << ", " << uBound << "): bound and diseq conflict" << std::endl;
        }
        // Value for var is now fixed
        result.fixed = true;
      }
    }
  }  

  return result;
}

bool CDBoundsModel::hasLowerBound(Variable var) const {
  return d_lowerBounds.find(var) != d_lowerBounds.end();
}

bool CDBoundsModel::hasUpperBound(Variable var) const {
  return d_upperBounds.find(var) != d_upperBounds.end();
}

bool CDBoundsModel::isFixed(Variable var) const {
 
  bound_map::const_iterator lfind = d_lowerBounds.find(var);
  if (lfind == d_lowerBounds.end()) return false;
  
  bound_map::const_iterator ufind = d_upperBounds.find(var);
  if (ufind == d_upperBounds.end()) return false;
  
  const BoundInfo& lbound = d_boundTrail[lfind->second];
  const BoundInfo& ubound = d_boundTrail[ufind->second];
  
  return !lbound.strict && !ubound.strict && lbound.value == ubound.value;  
}

const BoundInfo& CDBoundsModel::getLowerBoundInfo(Variable var) const {
  Assert(hasLowerBound(var));
  return d_boundTrail[d_lowerBounds.find(var)->second];
}

const BoundInfo& CDBoundsModel::getUpperBoundInfo(Variable var) const {
  Assert(hasUpperBound(var));
  return d_boundTrail[d_upperBounds.find(var)->second];
}

bool CDBoundsModel::inRange(Variable var, Rational value, bool& onlyOption) const {

  bool onUpperBound = false;
  bool onLowerBound = false;

  if (hasUpperBound(var)) {
    const BoundInfo& info = getUpperBoundInfo(var);
    if (info.strict) {
      if (value >= info.value) {
        return false;
      }
    } else {
      int cmp = value.cmp(info.value);
      if (cmp > 0) {
        return false;
      } else if (cmp == 0) {
        onUpperBound = true;
      }
    }
  }

  if (hasLowerBound(var)) {
    const BoundInfo& info = getLowerBoundInfo(var);
    if (info.strict) {
      if (value <= info.value) {
        return false;
      }
    } else {
      int cmp = value.cmp(info.value);
      if (cmp < 0) {
        return false;
      } else if (cmp == 0) {
        onLowerBound = true;
      }
    }
  }

  // It's the only option if on both bounds (reals)
  onlyOption = onUpperBound && onLowerBound;

  return true;
}

static Rational pickBinaryMean(const BoundInfo& l, const BoundInfo& u) {

  // Hm
  if (l.value == u.value) {
    return l.value;
  }

  // Get the biggest power of 2 between the two
  Rational m = (l.value + u.value)/2;
  Rational l1 = m.floor();
  Rational u1 = m.ceiling();

  if (l.strict) {
    if (l1 > l.value) {
      return l1;
    }
  } else {
    if (l1 >= l.value) {
      return l1;
    }
  }

  if (u.strict) {
    if (u1 < u.value) {
      return u1;
    }
  } else {
    if (u1 <= u.value) {
      return u1;
    }
  }

  do {
    // l1 < l <= u < u1 and l1 = p/2^k, l2 = (p+1)/2^k and no a/2^k solutions in [l, u]
    m = (l1 + u1)/2;
    // l1 < m < u1

    if (l.strict && m <= l.value) {
      l1 = m;
      continue;
    }
    if (!l.strict && m < l.value) {
      l1 = m;
      continue;
    }

    if (u.strict && m >= u.value) {
      u1 = m;
      continue;
    }
    if (!u.strict && m > u.value) {
      u1 = m;
      continue;
    }

    // Got it l <= m <= u
    break;

  } while (true);

  return m;
}

Rational CDBoundsModel::pick(Variable var, bool useCache) {

  Debug("mcsat::fm") << "CDBoundsModel::pick(" << var << ")" << std::endl;

  // Set of values to be disequal from
  std::set<Rational> disequal;
  getDisequal(var, disequal);

  // Return value
  Rational value;
  
  // Try the cached value
  if (useCache) {
    value = d_valueCache[var];
    if (inRange(var, value) && disequal.count(value) == 0) {
      Debug("mcsat::fm") << "FMPlugin::decide(): [cache] " << var << std::endl;
      ++ d_stats.pickCached;
      return value;
    }
  }

  // Try 0
  if (inRange(var, 0) && disequal.count(0) == 0) {
    ++ d_stats.pickZero;
    return 0;
  }

  if (hasLowerBound(var)) {
    const BoundInfo& lowerBound = getLowerBoundInfo(var);
    if (hasUpperBound(var)) {
      const BoundInfo& upperBound = getUpperBoundInfo(var);
      Debug("mcsat::fm") << "FMPlugin::decide(): " << var << " in [" << lowerBound.value << ".." << upperBound.value << "]" << std::endl;
      ++ d_stats.pickBoth;

      // Pick in the middle
      value = pickBinaryMean(lowerBound, upperBound);
      // Make sure it's not in the disequal set
      std::set<Rational>::const_iterator find = disequal.find(value);
      while (find != disequal.end()) {
        if (value < upperBound.value) {
          value = (value + upperBound.value) / 2;
        } else if (value > lowerBound.value) {
          value = (value + lowerBound.value) / 2;
        } else {
          Unreachable();
        }
        find = disequal.find(value);
      }
    } else {
      Debug("mcsat::fm") << "FMPlugin::decide(): " << var << " in [" << lowerBound.value << "..]" << std::endl;
      ++ d_stats.pickLower;
      // First int above + delta
      if (lowerBound.strict) {
        value = (lowerBound.value + 1).floor() + options::mcsat_fm_unbounded_d();
      } else {
        value = (lowerBound.value.ceiling()) + options::mcsat_fm_unbounded_d();
      }
      if (options::mcsat_fm_unbounded_sq()) {
	Rational p = 1;
	while (p < value) {
	  p *= 2;
	}
	value = p;
      }
      while (disequal.find(value) != disequal.end()) {
        value = value + 1;
      }
    }
  } else {
    // No lower bound
    if (hasUpperBound(var)) {
      ++ d_stats.pickUpper;
      const BoundInfo& upperBound = getUpperBoundInfo(var);
      Debug("mcsat::fm") << "FMPlugin::decide(): " << var << " in [.." << upperBound.value << "]" << std::endl;
      // First int below - delta
      if (upperBound.strict) {
        value = (upperBound.value -1).ceiling() - options::mcsat_fm_unbounded_d();
      } else {
        value = upperBound.value.floor() - options::mcsat_fm_unbounded_d();
      }
      if (options::mcsat_fm_unbounded_sq()) {
	Rational p = -1;
	while (p > value) {
	  p *= 2;
	}
	value = p;
      }
      while (disequal.find(value) != disequal.end()) {
        value = value - 1;
      }
    } else {
      ++ d_stats.pickNone;
      // No bounds, pick around 0
      value = 0;
      if (disequal.find(value) != disequal.end()) {
        unsigned d = 1;
        do {
          if (disequal.find(d) == disequal.end()) {
            value = d;
            break;
          }
          if (disequal.find(-d) == disequal.end()) {
            value = -d;
            break;
          }
          d ++;
        } while (true);
      }
    }
  }

  Debug("mcsat::fm") << "FMPlugin::decide(): picked " << value << std::endl;

  Assert(inRange(var, value));
  Assert(disequal.count(value) == 0);

  // Cache the values
  d_valueCache[var] = value;
  
  // Return the value
  return value;
}

bool CDBoundsModel::isDisequal(Variable var, Rational value) const {

  disequal_map::const_iterator find = d_disequalValues.find(var);
  if (find != d_disequalValues.end()) {
    // Go through all the values and check for the value
    DisequalInfoIndex it = find->second;
    while (it != null_diseqal_index) {
      const DisequalInfo& info = d_disequalTrail[it];
      if (info.value == value) {
        return true;
      } else {
        it = d_disequalTrailUndo[it].prev;
      }
    }
    // Seen all disequal values
    return false;
  } else {
    // Not asserted to be disequal to anything
    return false;
  }
}

void CDBoundsModel::getDisequal(Variable var, std::set<Rational>& disequal) const {
  disequal_map::const_iterator find = d_disequalValues.find(var);
  if (find != d_disequalValues.end()) {
    bool forced = false;
    // Go through all the values and check for the value
    Debug("mcsat::fm") << var << " !=";
    DisequalInfoIndex it = find->second;
    while (it != null_diseqal_index) {
      if (inRange(var, d_disequalTrail[it].value, forced)) {
        Assert(!forced);
        disequal.insert(d_disequalTrail[it].value);
	Debug("mcsat::fm") << " " << d_disequalTrail[it].value;
      }
      it = d_disequalTrailUndo[it].prev;
    }
    Debug("mcsat::fm") << std::endl;
  }
}

const DisequalInfo& CDBoundsModel::getDisequalInfo(Variable var, Rational value) const {

  DisequalInfoIndex found_index = null_diseqal_index;

  disequal_map::const_iterator find = d_disequalValues.find(var);
  if (find != d_disequalValues.end()) {
    // Go through all the values and check for the value
    Debug("mcsat::fm") << var << " !=";
    DisequalInfoIndex it = find->second;
    while (it != null_diseqal_index) {
      if (d_disequalTrail[it].value == value) {
        found_index = it;
      }
      it = d_disequalTrailUndo[it].prev;
    }
    Debug("mcsat::fm") << std::endl;
  }

  Assert(found_index != null_diseqal_index);
  return d_disequalTrail[found_index];
}
