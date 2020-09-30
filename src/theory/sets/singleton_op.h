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

#ifndef CVC4__SINGLETON_H
#define CVC4__SINGLETON_H

#include <iosfwd>
#include <memory>

namespace CVC4 {

class TypeNode;

class CVC4_PUBLIC SingletonOp
{
 public:
  /**
   * Constructs an singleton of the specified type. Note that the argument
   * is the type of the set itself, NOT the type of the elements.
   */
  SingletonOp(const TypeNode& setType);
  ~SingletonOp();
  SingletonOp(const SingletonOp& other);
  SingletonOp& operator=(const SingletonOp& other);

  const TypeNode& getType() const;
  bool operator==(const SingletonOp& es) const;
  bool operator!=(const SingletonOp& es) const;
  bool operator<(const SingletonOp& es) const;
  bool operator<=(const SingletonOp& es) const;
  bool operator>(const SingletonOp& es) const;
  bool operator>=(const SingletonOp& es) const;

 private:
  SingletonOp();

  std::unique_ptr<TypeNode> d_type;
}; /* class Singleton */

std::ostream& operator<<(std::ostream& out, const SingletonOp& es) CVC4_PUBLIC;

struct CVC4_PUBLIC SingletonOpHashFunction
{
  size_t operator()(const SingletonOp& es) const;
}; /* struct SingletonHashFunction */

}  // namespace CVC4

#endif /* CVC4__SINGLETON_H */
