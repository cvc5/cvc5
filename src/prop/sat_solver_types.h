/******************************************************************************
 * Top contributors (to current version):
 *   Dejan Jovanovic, Alex Ozdemir, Liana Hadarean
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * This class transforms a sequence of formulas into clauses.
 *
 * This class takes a sequence of formulas.
 * It outputs a stream of clauses that is propositionally
 * equi-satisfiable with the conjunction of the formulas.
 * This stream is maintained in an online fashion.
 *
 * Unlike other parts of the system it is aware of the PropEngine's
 * internals such as the representation and translation of [??? -Chris]
 */

#pragma once

#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "cvc5_private.h"

namespace cvc5::internal {
namespace prop {

/**
 * Boolean values of the SAT solver.
 */
enum SatValue {
  SAT_VALUE_UNKNOWN,
  SAT_VALUE_TRUE,
  SAT_VALUE_FALSE
};

/** Helper function for inverting a SatValue */
inline SatValue invertValue(SatValue v)
{
  if(v == SAT_VALUE_UNKNOWN) return SAT_VALUE_UNKNOWN;
  else if(v == SAT_VALUE_TRUE) return SAT_VALUE_FALSE;
  else return SAT_VALUE_TRUE;
}


/**
 * A variable of the SAT solver.
 */
typedef uint64_t SatVariable;

/**
 * Undefined SAT solver variable.
 */
const SatVariable undefSatVariable = SatVariable(-1);

/**
 * A SAT literal is a variable or an negated variable.
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
  SatLiteral()
  : d_value(undefSatVariable)
  {}

  /**
   * Construct a literal given a possible negated variable.
   */
  SatLiteral(SatVariable var, bool negated = false) {
    d_value = var + var + (int)negated;
  }

  /**
   * Returns the variable of the literal.
   */
  SatVariable getSatVariable() const {
    return d_value >> 1;
  }

  /**
   * Returns true if the literal is a negated variable.
   */
  bool isNegated() const {
    return d_value & 1;
  }

  /**
   * Negate the given literal.
   */
  SatLiteral operator ~ () const {
    return SatLiteral(getSatVariable(), !isNegated());
  }

  /**
   * Compare two literals for equality.
   */
  bool operator == (const SatLiteral& other) const {
    return d_value == other.d_value;
  }

  /**
   * Compare two literals for dis-equality.
   */
  bool operator != (const SatLiteral& other) const {
    return !(*this == other);
  }

  /**
   * Compare two literals
   */
  bool operator<(const SatLiteral& other) const
  {
    return getSatVariable() == other.getSatVariable()
               ? isNegated() < other.isNegated()
               : getSatVariable() < other.getSatVariable();
  }

  /**
   * Returns a string representation of the literal.
   */
  std::string toString() const {
    std::ostringstream os;
    os << (isNegated() ? "~" : "") << getSatVariable();
    return os.str();
  }

  /**
   * Returns the hash value of a literal.
   */
  size_t hash() const {
    return (size_t)d_value;
  }

  uint64_t toInt() const {
    return d_value; 
  }
  
  /**
   * Returns true if the literal is undefined.
   */
  bool isNull() const {
    return getSatVariable() == undefSatVariable;
  }
};

/**
 * A constant representing a undefined literal.
 */
const SatLiteral undefSatLiteral = SatLiteral(undefSatVariable);

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
 * Each object in the SAT solver, such as as variables and clauses, can be assigned a life span,
 * so that the SAT solver can (or should) remove them when the lifespan is over.
 */
enum SatSolverLifespan
{
  /**
   * The object should stay forever and never be removed
   */
  SAT_LIFESPAN_PERMANENT,
  /**
   * The object can be removed at any point when it becomes unnecessary.
   */
  SAT_LIFESPAN_REMOVABLE,
  /**
   * The object must be removed as soon as the SAT solver exits the search context
   * where the object got introduced.
   */
  SAT_LIFESPAN_SEARCH_CONTEXT_STRICT,
  /**
   * The object can be removed when SAT solver exits the search context where the object
   * got introduced, but can be kept at the solver discretion.
   */
  SAT_LIFESPAN_SEARCH_CONTEXT_LENIENT,
  /**
   * The object must be removed as soon as the SAT solver exits the user-level context where
   * the object got introduced.
   */
  SAT_LIFESPAN_USER_CONTEXT_STRICT,
  /**
   * The object can be removed when the SAT solver exits the user-level context where
   * the object got introduced.
   */
  SAT_LIFESPAN_USER_CONTEXT_LENIENT
};

}
}  // namespace cvc5::internal
