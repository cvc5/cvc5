#pragma once

#include "cvc4_private.h"

#include <set>
#include <vector>
#include <unordered_set>

#include <boost/static_assert.hpp>
#include <boost/integer/integer_mask.hpp>
#include <boost/functional/hash.hpp>

#include "expr/node.h"

namespace CVC4 {
namespace mcsat {
  
/**
 * A variable from a variable database. If refCount is true the references are
 * counted in the variable database. All variables with reference count 0 can
 * be reclaimed at search level 0. 
 */
class Variable {

public:
  
  /** Number of bits for the variable id */
  static const size_t BITS_FOR_VARIABLE_ID = 32;
  static const size_t BITS_FOR_TYPE_ID = 32;
  
  /** The null variable id */
  static const size_t s_null_varId = boost::low_bits_mask_t<BITS_FOR_VARIABLE_ID>::sig_bits;
  static const size_t s_null_typeId = boost::low_bits_mask_t<BITS_FOR_TYPE_ID>::sig_bits;

private:
  
  friend class VariableDatabase;

  /** Id of the variable */
  size_t d_varId     : BITS_FOR_VARIABLE_ID;
  size_t d_typeId    : BITS_FOR_TYPE_ID;

  /** Make a variable */
  Variable(size_t varId, size_t typeId)
  : d_varId(varId), d_typeId(typeId)
  {}
  
public:

  /** The null variable */
  static const Variable null;

  /** Is this a null variable */
  bool isNull() const {
    return d_varId == s_null_varId;
  }

  /** Creates a null variable */
  Variable()
  : d_varId(s_null_varId)
  , d_typeId(s_null_typeId)
  {}

  /** Copy constructor */
  Variable(const Variable& other)
  : d_varId(other.d_varId)
  , d_typeId(other.d_typeId)
  {}

  /** Assignment operator */
  Variable& operator = (const Variable& other) {
    if (this != &other) {
      d_varId = other.d_varId;
      d_typeId = other.d_typeId;
    }
    return *this;
  }

  /** Return a hash of the variable */
  size_t hash() const {
    typedef std::pair<size_t, size_t> int_pair;
    return boost::hash<int_pair>()(int_pair(d_typeId, d_varId));
  }

  /** Get the node associated with this variable (if any) */
  TNode getNode() const;

  /** Returns the type of the variable (if any) */
  TypeNode getTypeNode() const;

  /** Output to stream */
  void toStream(std::ostream& out) const;

  /** Comparison operator */
  bool operator < (const Variable& other) const {
    if (d_typeId == other.d_typeId) {
      return d_varId < other.d_varId;
    } else {
      return d_typeId < other.d_typeId;
    }
  }

  /** Comparison operator */
  bool operator == (const Variable& other) const {
    return d_typeId == other.d_typeId && d_varId == other.d_varId;
  }

  /** Comparison operator */
  bool operator != (const Variable& other) const {
    return !(*this == other);
  }
  
  /** Return the 0-based index of the variable of it's type */
  size_t index() const {
    return d_varId;
  }
  
  /** Return the 0-based index of the variables type */
  size_t typeIndex() const {
    return d_typeId;
  }
};

/** Output operator for variables */
inline std::ostream& operator << (std::ostream& out, const Variable& var) {
  var.toStream(out); 
  return out;
}

/** A vector of variables */
typedef std::vector<Variable> VariableVector;

/** A set of variables */
typedef std::set<Variable> VariableSet;

class VariableHashFunction {
public:
  size_t operator () (const Variable& variable) const {
    return variable.hash();
  }
};

/** A hash set of variables */
typedef std::unordered_set<Variable, VariableHashFunction> VariableHashSet;

inline std::ostream& operator << (std::ostream& out, const VariableVector& vars) {
  out << "Variables[";
  for (unsigned i = 0; i < vars.size(); ++ i) {
    if (i > 0) { out << ", "; }
    out << vars[i];
  }
  out << "]";
  return out;
}

inline std::ostream& operator << (std::ostream& out, const VariableSet& vars) {
  out << "Variables[";
  VariableSet::const_iterator it = vars.begin();
  bool first = true;
  for (; it != vars.end(); ++ it) {
    if (!first) { out << ", " << *it; }
    else { out << *it; first = false; }
  }
  out << "]";
  return out;
}

inline std::ostream& operator << (std::ostream& out, const VariableHashSet& vars) {
  out << "Variables[";
  VariableHashSet::const_iterator it = vars.begin();
  bool first = true;
  for (; it != vars.end(); ++ it) {
    if (!first) { out << ", " << *it; }
    else { out << *it; first = false; }
  }
  out << "]";
  return out;
}


} /* Namespace mcsat */
} /* Namespace CVC4 */
