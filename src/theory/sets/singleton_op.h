/*********************                                                        */
/*! \file singleton_op.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief a class for singleton operator for sets
 **/

#include "cvc4_public.h"

#ifndef CVC4__SINGLETON_OP_H
#define CVC4__SINGLETON_OP_H

#include <memory>

namespace CVC4 {

class TypeNode;

/**
 * The class is an operator for kind SINGLETON used to construct singleton sets.
 * It specifies the type of the single element especially when it is a constant.
 * e.g. the type of rational 1 is Int, however
 * (singleton (singleton_op Real) 1) is of type (Set Real), not (Set Int).
 * Note that the type passed to the constructor is the element's type, not the
 * set type.
 */
class SingletonOp
{
 public:
  SingletonOp(const TypeNode& elementType);
  SingletonOp(const SingletonOp& op);

  /** return the type of the current object */
  const TypeNode& getType() const;

  bool operator==(const SingletonOp& op) const;

 private:
  SingletonOp();
  /** a pointer to the type of the singleton element */
  std::unique_ptr<TypeNode> d_type;
}; /* class Singleton */

std::ostream& operator<<(std::ostream& out, const SingletonOp& op);

/**
 * Hash function for the SingletonHashFunction objects.
 */
struct CVC4_PUBLIC SingletonOpHashFunction
{
  size_t operator()(const SingletonOp& op) const;
}; /* struct SingletonOpHashFunction */

}  // namespace CVC4

#endif /* CVC4__SINGLETON_OP_H */
