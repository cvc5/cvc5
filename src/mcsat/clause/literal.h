#pragma once

#include "cvc4_private.h"

#include <iostream>
#include <tr1/functional>
#include <boost/static_assert.hpp>

#include <unordered_set>

#include "mcsat/variable/variable.h"

namespace CVC4 {
namespace mcsat {


/** Literal encapsulates a variable and whether it is negated or not */
class Literal {

  /** The variable */
  Variable d_variable;

  /** Is the variable negated */
  bool d_negated;
  
public:

  /** The null literal */
  static const Literal null;

  /** Construct the literal given the variable and whether it is negated */
  Literal(Variable var, bool negated)
  : d_variable(var)
  , d_negated(negated)
  {
  }

  /** Construct a null literal */
  Literal()
  : d_variable(), d_negated(0) {}

  /** Copy constructor */
  Literal(const Literal& other)
  : d_variable(other.d_variable)
  , d_negated(other.d_negated)
  {}

  /** Assignment */
  Literal& operator = (const Literal& other) {
    if (this != &other) {
      d_variable = other.d_variable;
      d_negated = other.d_negated;
    }
    return *this;
  }

  /** Return the variable of the literal */
  Variable getVariable() const { return d_variable; }

  /** Is it a null literal */
  bool isNull() const { return d_variable.isNull(); }

  /** Return true if the literal is negated */
  bool isNegated() const { return d_negated; }

  /** Return true if hte literal is the negation of the given literal */
  bool isNegationOf(const Literal& lit) const {
    if (d_variable != lit.d_variable) return false;
    return d_negated != lit.d_negated;
  }

  /** Negate this literal */
  void negate() { d_negated = !d_negated; }

  /** Return the nagation of this literal */
  Literal operator ~ () const {
    return Literal(d_variable, !d_negated);
  }

  /** 0-based index of the literal */
  size_t index() const {
    return (d_variable.index() << 1) | (d_negated ? 1 : 0);
  }

  /** Compare with some other literal */
  bool operator == (const Literal& other) const {
    return index() == other.index();
  }

  /** Compare with some other literal */
  bool operator != (const Literal& other) const {
    return index() != other.index();
  }

  /** Compare with some other literal */
  bool operator < (const Literal& other) const {
    return index() < other.index();
  }

  /** Simple stream representation */
  void toStream(std::ostream& out) const {
    if (d_negated) {
      out << "~";
    }
    out << d_variable;
  }

  /** Hash of the literal */
  size_t hash() const {
    return std::tr1::hash<unsigned>()(index());
  }
};

/** Vector of literals */
typedef std::vector<Literal> LiteralVector;

/** Set of literals */
typedef std::set<Literal> LiteralSet;

class LiteralHashFunction {
public:
  size_t operator () (const Literal& l) const {
    return l.hash();
  }
};

/** Hash-set of literals */
typedef std::unordered_set<Literal, LiteralHashFunction> LiteralHashSet;

/** Output operator for a literal */
inline std::ostream& operator << (std::ostream& out, const Literal& lit) {
  lit.toStream(out);
  return out;
}

inline std::ostream& operator << (std::ostream& out, const LiteralVector& literals) {
  out << "Literals[";
  for (unsigned i = 0; i < literals.size(); ++ i) {
    if (i > 0) { out << ", "; }
    out << literals[i];
  }
  out << "]";
  return out;
}

inline std::ostream& operator << (std::ostream& out, const LiteralSet& literals) {
  out << "Literals[";
  LiteralSet::const_iterator it = literals.begin();
  bool first = true;
  for (; it != literals.end(); ++ it) {
    if (!first) { out << ", " << *it; }
    else { out << *it; first = false; }
  }
  out << "]";
  return out;
}

inline std::ostream& operator << (std::ostream& out, const LiteralHashSet& literals) {
  out << "Literals[";
  LiteralHashSet::const_iterator it = literals.begin();
  bool first = true;
  for (; it != literals.end(); ++ it) {
    if (!first) { out << ", " << *it; }
    else { out << *it; first = false; }
  }
  out << "]";
  return out;
}

}
}
