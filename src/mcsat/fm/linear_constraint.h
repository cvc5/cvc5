#pragma once

#include "expr/node.h"
#include "mcsat/variable/variable.h"
#include "mcsat/clause/literal.h"
#include "mcsat/fm/bound_info.h"

#include <vector>
#include <iostream>
#include <unordered_map>

namespace CVC4 {
namespace mcsat {

class SolverTrail;

namespace fm {

/** Pair of a variable and a rational */
typedef std::pair<Variable, Rational> var_rational_pair;

/** Map from variables to coefficients, null is the constant term */
typedef std::unordered_map<Variable, Rational, VariableHashFunction> var_to_rational_map;

typedef std::vector<var_rational_pair> var_rational_pair_vector;

/** Information about a bound */
struct BoundingInfo {
  /** The value of the bound */
  Rational value;
  /** The kind of bound */
  Kind kind;

  BoundingInfo(Rational value, Kind kind)
  : value(value), kind(kind) {}

  BoundingInfo()
  : value(0), kind(kind::UNDEFINED_KIND)
  {}

  void swap(BoundingInfo& other) {
    std::swap(value, other.value);
    std::swap(kind, other.kind);
  }

  /** Clear */
  void clear() {
    value = 0;
    kind = kind::UNDEFINED_KIND;
  }

  /** As if the constraint was negated */
  void negate();

  /** Is this a lower bound */
  bool isLowerBound() const {
    switch(kind) {
    case kind::GT:
    case kind::GEQ:
    case kind::EQUAL:
      return true;
    default:
      return false;
    }
  }

  /** Is this an upper bound */
  bool isUpperBound() const {
    switch(kind) {
    case kind::LT:
    case kind::LEQ:
    case kind::EQUAL:
      return true;
    default:
      return false;

    }
  }

  /** Is this a strict bound */
  bool isStrict() const {
    return kind == kind::LT || kind == kind::GT;
  }
};

/**
 * A generic linear constraint (t op 0) is just a map from variables to coefficients
 * representing a term t, and a kind of constraint op. The resulting constraint will
 * be of kind either >=, >, ==, or !=.
 */
class LinearConstraint {

  /** Coefficients and variables */
  var_rational_pair_vector d_coefficients;

  /** The kind of constraint >=, ... */
  Kind d_kind;

  /** Evaluation timestamp */
  size_t d_evaluationTimestamp;

  /** Evaluation cached value */
  bool d_evaluationCache;
  
  /** Bounding timestamp */
  size_t d_boundingTimestamp;

  /** The variable we whose value we cached */
  Variable d_boundingVariable;

  /** Bounding cached value */
  BoundingInfo d_boundingCache;

  static void normalize(var_rational_pair_vector& coefficients);

  static bool parse(TNode constraint, Rational mult, var_rational_pair_vector& coefficientMap);

  void clearCache();

public:

  /** Default constructor (null constraint) */
  LinearConstraint();

  /** Clears the constraint */
  void clear();

  /** Null constraint ? */
  bool isNull() const;
  
  /** Returns the number of proper variables */
  unsigned size() const {
    return d_coefficients.size() - 1;
  }

  /** Get the variables of this constraint */
  void getVariables(std::vector<Variable>& vars) const;

  /** Get the variables of this constraint */
  void getVariables(std::set<Variable>& vars) const;

  /** Get the top variable */
  Variable getTopVariable(const SolverTrail& trail) const;
  
  /** Get the first unassigned variable */
  Variable getUnassignedVariable(const SolverTrail& trail) const;
  
  /** Get the kind of the constraint */
  Kind getKind() const {
    return d_kind;
  }

  /** Swap with the given constraint */
  void swap(LinearConstraint& c);

  /** Output to stream */
  void toStream(std::ostream& out) const;

  /**
   * Evaluate the constraint in the trail (true, false). It returns the level at which
   * the constraint evaluates.
   */
  bool evaluate(const SolverTrail& trail, unsigned& level) const;

  bool evaluate(const SolverTrail& trail) const {
    unsigned level;
    return evaluate(trail, level);
  }

  /**
   * Returns the constraint evaluates, or -1 otherwise.
   */
  int getEvaluationLevel(const SolverTrail& trail) const;

  /**
   * Bounds a variable in the given context unsing this constraint.
   */
  BoundingInfo bound(Variable x, const SolverTrail& trail) const;
  
  typedef var_rational_pair_vector::const_iterator const_iterator;

  /** Returns the cosfficient with the given variable */
  Rational getCoefficient(Variable var) const;
  
  const_iterator begin() const {
    return d_coefficients.begin();
  }

  const_iterator end() const {
    return d_coefficients.end();
  }

  /**
   * Return the literal representation of the constraint. If the literal does 
   * not exist yet, it will be created hence spawning notifications.
   */
  Literal getLiteral(const SolverTrail& trail) const;
  
  /** 
   * Multiply the constraint with the given positive constant.
   */
  void multiply(Rational c);
  
  /**
   * Multiply an (dis-)equality with -1.
   */
  void flipEquality();
  
  /**
   * Split this disequality ax + t != 0 into
   *  [this]    |a| x + p > 0 and
   *  [other]  -|a| x - p > 0
   */
  void splitDisequality(Variable x, LinearConstraint& other);

  /** 
   * Add the given linear constraint multiplied with the given positive 
   * factor.
   */
  void add(const LinearConstraint& other, Rational c = 1);
  
  /** 
   * Parse a literal into a linear constraint. Returns true if successful. The
   * result of the parse will always be a constraint of type t > 0, t >= 0, 
   * t = 0, ot t != 0, i.e. t < 0 and t <= are parsed in as -t > 0 and -t >= 0. 
   */
  static bool parse(Literal constraint, LinearConstraint& out);

  /** Negates the kind as if the linear constraint was negated */
  static Kind negateKind(Kind kind);

  /** Flips the kind as if the linear constraint was multiplied with -1 */
  static Kind flipKind(Kind kind);

};

inline std::ostream& operator << (std::ostream& out, const LinearConstraint& c) {
  c.toStream(out);
  return out;
}


}
}
}





