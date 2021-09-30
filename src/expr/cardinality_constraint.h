/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5 {

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
  CardinalityConstraint(const TypeNode& setType, const Integer& ub);
  ~CardinalityConstraint();
  CardinalityConstraint(const CardinalityConstraint& other);
  CardinalityConstraint& operator=(const CardinalityConstraint& other);

  /** Get the type of the cardinality constraint */
  const TypeNode& getType() const;
  /** Get the upper bound value of the cardinality constraint */
  const Integer& getUpperBound() const;

  bool operator==(const CardinalityConstraint& cc) const;
  bool operator!=(const CardinalityConstraint& cc) const;
  bool operator<(const CardinalityConstraint& cc) const;
  bool operator<=(const CardinalityConstraint& cc) const;
  bool operator>(const CardinalityConstraint& cc) const;
  bool operator>=(const CardinalityConstraint& cc) const;

 private:
  CardinalityConstraint();

  std::unique_ptr<TypeNode> d_type;
  const Integer d_ubound;
};

std::ostream& operator<<(std::ostream& out, const CardinalityConstraint& cc);

}  // namespace cvc5

#endif /* CVC5__EXPR__CARDINALITY_CONSTRAINT_H */
