#pragma once

#include "expr/node.h"
#include "context/cdo.h"
#include "mcsat/variable/variable.h"
#include "mcsat/fm/bound_info.h"
#include "mcsat/fm/linear_constraint.h"
#include "util/statistics_registry.h"

#include <unordered_map>

#include <iostream>
#include <boost/integer_traits.hpp>

namespace CVC4 {
namespace mcsat {
namespace fm {

/** Statistics for the value selection */
struct BoundStats {
  /** Number of 0 selections */
  IntStat pickZero;
  /** Number of cached selections */
  IntStat pickCached;
  /** Number of .[..]. selections */
  IntStat pickBoth;
  /** Number of [.... selections */
  IntStat pickLower;
  /** Number of ....] selections */
  IntStat pickUpper;
  /** Number of .... selections */
  IntStat pickNone;
 
  StatisticsRegistry* d_registry;
 
  BoundStats(StatisticsRegistry* registry) 
  : pickZero("mcsat::fm::value_zero", 0)
  , pickCached("mcsat::fm::value_cached", 0)
  , pickBoth("mcsat::fm::value_both", 0)
  , pickLower("mcsat::fm::value_lower", 0)
  , pickUpper("mcsat::fm::value_upper", 0)
  , pickNone("mcsat::fm::value_none", 0)
  , d_registry(registry)
  {
    d_registry->registerStat(&pickZero);
    d_registry->registerStat(&pickCached);
    d_registry->registerStat(&pickBoth);
    d_registry->registerStat(&pickLower);
    d_registry->registerStat(&pickUpper);
    d_registry->registerStat(&pickNone);
  }
  
  ~BoundStats() {
    d_registry->unregisterStat(&pickZero);
    d_registry->unregisterStat(&pickCached);
    d_registry->unregisterStat(&pickBoth);
    d_registry->unregisterStat(&pickLower);
    d_registry->unregisterStat(&pickUpper);
    d_registry->unregisterStat(&pickNone);
  }
};

/** Value info for stating x != value */
struct DisequalInfo {
  /** The value itself */
  Rational value;
  /** The reason for this bound */
  Variable reason;

  DisequalInfo() {}

  DisequalInfo(Rational value, Variable reason)
  : value(value), reason(reason)
  {}

  void toStream(std::ostream& out) const {
    out << value;
  }
};

inline std::ostream& operator << (std::ostream& out, const DisequalInfo& info) {
  info.toStream(out);
  return out;
}

/** Compare two constraints that imply the same bound */
class IConstraintDiscriminator {
public:
  virtual ~IConstraintDiscriminator() {}
  /** Is c1 better than c2 */
  virtual bool better(Variable c1, Variable c2) = 0;
};

/** Context-dependent bounds model */
class CDBoundsModel : public context::ContextNotifyObj {

  /** Some stats */
  BoundStats d_stats;
  
  /** Index of the bound in the bounds vector */
  typedef unsigned BoundInfoIndex;
  
  /** Null bound index */
  static const BoundInfoIndex null_bound_index = boost::integer_traits<BoundInfoIndex>::const_max;
  
  /** Map from variables to the index of the bound information in the bound trail */
  typedef std::unordered_map<Variable, BoundInfoIndex, VariableHashFunction> bound_map;
    
  /** Lower bounds map */
  bound_map d_lowerBounds;
  
  /** Upper bounds map */
  bound_map d_upperBounds;

  /** Map from variables to their cached values */
  typedef std::unordered_map<Variable, Rational, VariableHashFunction> var_to_rational_map;
  
  /** Cache of values */
  var_to_rational_map d_valueCache;
  
  /** Bound update trail (this is where the actual bounds are) */
  std::vector<BoundInfo> d_boundTrail;

  /** Information for undoing */
  struct UndoBoundInfo {
    /** Which variable to undo */
    Variable var;
    /** Index of the previous bound (null if none) */
    BoundInfoIndex prev;
    /** Is it a lower bound */
    bool isLower;
    
    UndoBoundInfo()
    : prev(null_bound_index), isLower(false) {}
    
    UndoBoundInfo(Variable var, BoundInfoIndex prev, bool isLower)
    : var(var), prev(prev), isLower(isLower) {}      
  };
  
  /** Bound update trail (same size as d_boundTrail) */
  std::vector<UndoBoundInfo> d_boundTrailUndo;
  
  /** Count of lower bound updates */
  context::CDO<unsigned> d_boundTrailSize;

  /** Index of the value in the value list */
  typedef unsigned DisequalInfoIndex;

  /** Null value list index index */
  static const DisequalInfoIndex null_diseqal_index = boost::integer_traits<DisequalInfoIndex>::const_max;

  /** Map from variables to the head of their value list */
  typedef std::unordered_map<Variable, DisequalInfoIndex, VariableHashFunction> disequal_map;

  /** The map from variables to it's diseqality lists */
  disequal_map d_disequalValues;

  /** Trail of disequality information */
  std::vector<DisequalInfo> d_disequalTrail;

  /** Var != value, and link to the previous dis-equality */
  struct UndoDisequalInfo {
    /** Which variable */
    Variable var;
    /** INdex of the previsous disequal info */
    DisequalInfoIndex prev;

    UndoDisequalInfo()
    : prev(null_diseqal_index) {}

    UndoDisequalInfo(Variable var, DisequalInfoIndex prev)
    : var(var), prev(prev) {}

  };

  /** Values */
  std::vector<UndoDisequalInfo> d_disequalTrailUndo;

  /** Size of the values trail */
  context::CDO<unsigned> d_disequalTrailSize;

  /** Variables that are in conflict */
  std::set<Variable> d_variablesInConflict;
  
  /** Update to the appropriate context state */
  void contextNotifyPop();
  
  /**
   * Is the value in the range of the bounds.
   * @oaram onlyOption if in range and this is the only available option => true
   */
  bool inRange(Variable var, Rational value, bool& onlyOption) const;

  bool inRange(Variable var, Rational value) const {
    bool onlyOption;
    return inRange(var, value, onlyOption);
  }
  
  /**
   * Check whether variable is asserted to be different from the given constant.
   */
  bool isDisequal(Variable var, Rational value) const;

  /**
   * Get the set of all the values that are asserted to be disequal from var.
   */
  void getDisequal(Variable var, std::set<Rational>& disequal) const;

  /** Compare constraints somehow */
  IConstraintDiscriminator* d_constraintCMP;

  /** Do we improve the lower bound */
  bool improvesLowerBound(Variable var, const BoundInfo& info) const;

  /** Do we improve the upper bound  */
  bool improvesUpperBound(Variable var, const BoundInfo& info) const;

public:
  
  ~CDBoundsModel(){}
  
  /** Construct it */
  CDBoundsModel(context::Context* context, StatisticsRegistry* registry);
  
  struct update_info {
    /** Did the update actually update */
    bool updated;
    /** Did the update fix the variabel to a value */
    bool fixed;

    update_info(bool updated = false, bool fixed = false)
    : updated(updated), fixed(fixed) {}

  };

  /** Update the lower bound, returns true if variable is now fixed */
  update_info updateLowerBound(Variable var, const BoundInfo& info);

  /** Update the upper bound, returns true if variable is now fixed */
  update_info updateUpperBound(Variable var, const BoundInfo& info);

  /** If two constraints imply the same bound, which one to keep */
  void setDiscriminator(IConstraintDiscriminator* d) {
    d_constraintCMP = d;
  }

  /** Adds the value to the list of values that a variable must be disequal from */
  void addDisequality(Variable var, const DisequalInfo& info);

  /** Does the variable have a lower bound */
  bool hasLowerBound(Variable var) const;

  /** Does the variable have an upper bound */
  bool hasUpperBound(Variable var) const;
  
  /** Is this variable fixed by it's upper and lower bound */
  bool isFixed(Variable var) const;
  
  /** Pick a value for a variable */
  Rational pick(Variable var, bool useCache);

  /** Get the current lower bound info */
  const BoundInfo& getLowerBoundInfo(Variable var) const;

  /** Get the current upper bound info */
  const BoundInfo& getUpperBoundInfo(Variable var) const;
  
  /** Get the information about the disequality */
  const DisequalInfo& getDisequalInfo(Variable var, Rational value) const;

  /** Is the state of bounds in conflict */
  bool inConflict() const {
    return d_variablesInConflict.size() > 0;
  }
  
  /** Get the variables with conflicting bound */
  void getVariablesInConflict(std::set<Variable>& out) {
    out.swap(d_variablesInConflict);
  }
};

} // fm namespace
}
}



