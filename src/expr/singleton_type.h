/*********************                                                        */
/*! \file singleton.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andres Noetzli, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef CVC4__SINGLETON_H
#define CVC4__SINGLETON_H

#include <iosfwd>
#include <memory>

namespace CVC4 {

class TypeNode;

class CVC4_PUBLIC SingletonType
{
 public:
  /**
   * Constructs an singleton of the specified type. Note that the argument
   * is the type of the set itself, NOT the type of the elements.
   */
  SingletonType(const TypeNode& setType);
  ~SingletonType();
  SingletonType(const SingletonType& other);
  SingletonType& operator=(const SingletonType& other);

  const TypeNode& getType() const;
  bool operator==(const SingletonType& es) const;
  bool operator!=(const SingletonType& es) const;
  bool operator<(const SingletonType& es) const;
  bool operator<=(const SingletonType& es) const;
  bool operator>(const SingletonType& es) const;
  bool operator>=(const SingletonType& es) const;

 private:
  SingletonType();

  std::unique_ptr<TypeNode> d_type;
}; /* class Singleton */

std::ostream& operator<<(std::ostream& out, const SingletonType& es) CVC4_PUBLIC;

struct CVC4_PUBLIC SingletonTypeHashFunction
{
  size_t operator()(const SingletonType& es) const;
}; /* struct SingletonHashFunction */

}  // namespace CVC4

#endif /* CVC4__SINGLETON_H */
