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
 * A class for representing abstract types.
 */

#include "cvc5_public.h"

#ifndef CVC5__THEORY__BUILTIN__ABSTRACT_TYPE_H
#define CVC5__THEORY__BUILTIN__ABSTRACT_TYPE_H

#include "expr/kind.h"

namespace cvc5::internal {

/**
 * The payload for abstract types, which carries a kind specifying the kind
 * of type this abstract type abstracts.
 */
class AbstractType
{
 public:
  AbstractType(Kind k);
  AbstractType(const AbstractType& op);

  /** Return the kind of sort that this abstract type abstracts */
  Kind getKind() const;

  bool operator==(const AbstractType& op) const;

 private:
  AbstractType();
  /** The kind of sort that this sort abstracts */
  Kind d_kind;
}; /* class AbstractType */

std::ostream& operator<<(std::ostream& out, const AbstractType& op);

/**
 * Hash function for the AbstractType objects.
 */
struct AbstractTypeHashFunction
{
  size_t operator()(const AbstractType& op) const;
}; /* struct AbstractTypeHashFunction */

}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BUILTIN__APPLY_ABSTRACT_OP_H */
