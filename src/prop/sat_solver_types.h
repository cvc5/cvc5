/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SAT solver types and type operations.
 */

#pragma once

#include <ostream>
#include <string>
#include <unordered_set>
#include <vector>

#include "cvc5_private.h"

namespace cvc5::internal {
namespace prop {

class SatSolver;

/**
 * Boolean values of the SAT solver.
 */
enum SatValue : uint8_t {
  SAT_VALUE_UNKNOWN,
  SAT_VALUE_TRUE,
  SAT_VALUE_FALSE
};

/** Helper function for inverting a SatValue */
constexpr SatValue invertValue(const SatValue v)
{
  if(v == SAT_VALUE_UNKNOWN) return SAT_VALUE_UNKNOWN;
  return v == SAT_VALUE_TRUE ? SAT_VALUE_FALSE : SAT_VALUE_TRUE;
}

constexpr SatValue operator~(const SatValue v)
{
  return invertValue(v);
}

/**
 * A variable of the SAT solver.
 */
typedef uint64_t SatVariable;

/**
 * Undefined SAT solver variable.
 */
constexpr SatVariable undefSatVariable = static_cast<SatVariable>(-1);

/**
 * A SAT literal is a variable or a negated variable.
 */
class SatLiteral {

  /**
   * The value holds the variable and a bit noting if the variable is negated.
   */
  uint64_t d_value;

 public:

  /**
   * Construct an undefined SAT literal.
   */
  constexpr SatLiteral() : SatLiteral(undefSatVariable) {}

  /**
   * Construct a literal given a possible negated variable.
   */
  constexpr explicit SatLiteral(SatVariable var, bool negated = false)
      : d_value(var + var + static_cast<int>(negated))
  {
  }

  /**
   * Returns the variable of the literal.
   */
  constexpr SatVariable getSatVariable() const {
    // sign extension shift to ensure that undefSatLiteral has undefSatVariable
    return static_cast<int64_t>(d_value) >> 1;
  }

  /**
   * Returns true if the literal is a negated variable.
   */
  constexpr bool isNegated() const {
    return d_value & 1;
  }

  /**
   * Negate the given literal.
   */
  constexpr SatLiteral operator ~ () const {
    return SatLiteral(getSatVariable(), !isNegated());
  }

  /**
   * Compare two literals for equality.
   */
  constexpr bool operator == (const SatLiteral& other) const {
    return d_value == other.d_value;
  }

  /**
   * Compare two literals for dis-equality.
   */
  constexpr bool operator != (const SatLiteral& other) const {
    return !(*this == other);
  }

  /**
   * Compare two literals
   */
  constexpr bool operator<(const SatLiteral& other) const
  {
    return getSatVariable() == other.getSatVariable()
               ? isNegated() < other.isNegated()
               : getSatVariable() < other.getSatVariable();
  }

  /**
   * Returns a string representation of the literal.
   */
  std::string toString() const {
    return std::string(isNegated() ? "~" : "") + std::to_string(getSatVariable());
  }

  /**
   * Returns the hash value of a literal.
   */
  constexpr size_t hash() const {
    return (size_t)d_value;
  }

  constexpr uint64_t toInt() const {
    return d_value; 
  }
  
  /**
   * Returns true if the literal is undefined.
   */
  constexpr bool isNull() const {
    return getSatVariable() == undefSatVariable;
  }
};

/**
 * A constant representing an undefined literal.
 */
constexpr SatLiteral undefSatLiteral = SatLiteral(undefSatVariable);

static_assert(undefSatLiteral.getSatVariable() == undefSatVariable);
static_assert(undefSatLiteral.isNull());
static_assert(SatLiteral() == undefSatLiteral);

/**
 * Helper for hashing the literals.
 */
struct SatLiteralHashFunction {
  inline size_t operator() (const SatLiteral& literal) const {
    return literal.hash();
  }
};

/**
 * A SAT clause is a vector of literals.
 */
typedef std::vector<SatLiteral> SatClause;

struct SatClauseSetHashFunction
{
  inline size_t operator()(
      const std::unordered_set<SatLiteral, SatLiteralHashFunction>& clause)
      const
  {
    size_t acc = 0;
    for (const auto& l : clause)
    {
      acc ^= l.hash();
    }
    return acc;
  }
};

struct SatClauseLessThan
{
  bool operator()(const SatClause& l, const SatClause& r) const;
};

/**
 * Printing functions for Sat types.
 */

inline std::ostream& operator <<(std::ostream& out, SatLiteral lit) {
  out << lit.toString();
  return out;
}

inline std::ostream& operator <<(std::ostream& out, const SatClause& clause) {
  out << "clause:";
  for(unsigned i = 0; i < clause.size(); ++i) {
    out << " " << clause[i];
  }
  out << ";";
  return out;
}

inline std::ostream& operator <<(std::ostream& out, SatValue val) {
  switch(val) {
    case SAT_VALUE_UNKNOWN:
      out << '_';
      break;
    case SAT_VALUE_TRUE:
      out << '1';
      break;
    case SAT_VALUE_FALSE:
      out << '0';
      break;
    default:
      out << "Error";
      break;
  }
  return out;
}

}
}  // namespace cvc5::internal
