/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for singleton operator for sets.
 */

#include "cvc5_public.h"

#ifndef CVC5__THEORY__SETS__SINGLETON_OP_H
#define CVC5__THEORY__SETS__SINGLETON_OP_H

#include <memory>

namespace cvc5 {

class TypeNode;

/**
 * The class is an operator for kind SET_SINGLETON used to construct singleton
 * sets. It specifies the type of the single element especially when it is a
 * constant. e.g. the type of rational 1 is Int, however (singleton
 * (singleton_op Real) 1) is of type (Set Real), not (Set Int). Note that the
 * type passed to the constructor is the element's type, not the set type.
 */
class SetSingletonOp
{
 public:
  SetSingletonOp(const TypeNode& elementType);
  SetSingletonOp(const SetSingletonOp& op);

  /** return the type of the current object */
  const TypeNode& getType() const;

  bool operator==(const SetSingletonOp& op) const;

 private:
  SetSingletonOp();
  /** a pointer to the type of the singleton element */
  std::unique_ptr<TypeNode> d_type;
}; /* class SetSingletonOp */

std::ostream& operator<<(std::ostream& out, const SetSingletonOp& op);

/**
 * Hash function for the SetSingletonOp objects.
 */
struct SetSingletonOpHashFunction
{
  size_t operator()(const SetSingletonOp& op) const;
}; /* struct SetSingletonOpHashFunction */

}  // namespace cvc5

#endif /* CVC5__THEORY__SETS__SINGLETON_OP_H */
