/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cardinality constraint operator
 */

#include "cvc5_public.h"

#ifndef CVC5__EXPR__CARDINALITY_CONSTRAINT_H
#define CVC5__EXPR__CARDINALITY_CONSTRAINT_H

#include <iosfwd>
#include <memory>

#include "util/integer.h"
#include "util/hash.h"

namespace cvc5::internal {

class TypeNode;

/**
 * A cardinality constraint, handled in the cardinality extension of the UF
 * solver, used for finite model finding.
 */
class CardinalityConstraint
{
 public:
  /**
   * Constructs a cardinality constraint of the specified type, which should
   * be an uninterpreted sort.
   */
  CardinalityConstraint(const TypeNode& ufType, const Integer& ub);
  ~CardinalityConstraint();
  CardinalityConstraint(const CardinalityConstraint& other);

  /** Get the type of the cardinality constraint */
  const TypeNode& getType() const;
  /** Get the upper bound value of the cardinality constraint */
  const Integer& getUpperBound() const;

  bool operator==(const CardinalityConstraint& cc) const;
  bool operator!=(const CardinalityConstraint& cc) const;

 private:
  /** The type that the cardinality constraint is for */
  std::unique_ptr<TypeNode> d_type;
  /** The upper bound on the cardinality of the above type */
  const Integer d_ubound;
};

std::ostream& operator<<(std::ostream& out, const CardinalityConstraint& cc);

struct CardinalityConstraintHashFunction
{
  size_t operator()(const CardinalityConstraint& cc) const;
};

/**
 * A combined cardinality constraint, handled in the cardinality extension of
 * the UF solver, used for finite model finding for bounding the sum of
 * cardinalities of all uninterpreted sorts.
 */
class CombinedCardinalityConstraint
{
 public:
  /**
   * Constructs a cardinality constraint of the specified type, which should
   * be an uninterpreted sort.
   */
  CombinedCardinalityConstraint(const Integer& ub);
  ~CombinedCardinalityConstraint();
  CombinedCardinalityConstraint(const CombinedCardinalityConstraint& other);

  /** Get the upper bound value of the cardinality constraint */
  const Integer& getUpperBound() const;

  bool operator==(const CombinedCardinalityConstraint& cc) const;
  bool operator!=(const CombinedCardinalityConstraint& cc) const;

 private:
  /** The upper bound on the cardinality of the above type */
  const Integer d_ubound;
};

std::ostream& operator<<(std::ostream& out,
                         const CombinedCardinalityConstraint& cc);

struct CombinedCardinalityConstraintHashFunction
{
  size_t operator()(const CombinedCardinalityConstraint& cc) const;
};

}  // namespace cvc5::internal

#endif
