/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class representing a parameter for the type ascription operator.
 */

#include "cvc5_public.h"

#ifndef CVC5__ASCRIPTION_TYPE_H
#define CVC5__ASCRIPTION_TYPE_H

#include <iosfwd>
#include <memory>

namespace cvc5::internal {

class TypeNode;

/**
 * A class used to parameterize a type ascription.  For example,
 * "nil :: list<nat>" is an expression of kind APPLY_TYPE_ASCRIPTION.
 * The parameter is an ASCRIPTION_TYPE-kinded expression with an
 * AscriptionType payload.  (Essentially, all of this is a way to
 * coerce a Type into the expression tree.)
 */
class AscriptionType
{
 public:
  AscriptionType(TypeNode t);
  ~AscriptionType();
  AscriptionType(const AscriptionType& other);
  AscriptionType& operator=(const AscriptionType& other);
  TypeNode getType() const;
  bool operator==(const AscriptionType& other) const;
  bool operator!=(const AscriptionType& other) const;

 private:
  /** The type */
  std::unique_ptr<TypeNode> d_type;
}; /* class AscriptionType */

/**
 * A hash function for type ascription operators.
 */
struct AscriptionTypeHashFunction
{
  size_t operator()(const AscriptionType& at) const;
}; /* struct AscriptionTypeHashFunction */

/** An output routine for AscriptionTypes */
std::ostream& operator<<(std::ostream& out, AscriptionType at);

}  // namespace cvc5::internal

#endif /* CVC5__ASCRIPTION_TYPE_H */
