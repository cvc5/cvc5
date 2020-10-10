/*********************                                                        */
/*! \file arith.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andres Noetzli, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utils for arithmetic kinds.
 **
 ** Some utils for arithmetic kinds, for example indexed root predicates.
 **/

#include "cvc4_public.h"

#ifndef CVC4__UTIL__ARITH_H
#define CVC4__UTIL__ARITH_H

namespace CVC4 {

/**
 * The structure representing a root predicate.
 */
struct CVC4_PUBLIC IndexedRootPredicate
{
  /** The index of the root */
  unsigned d_index;

  IndexedRootPredicate(unsigned index) : d_index(index) {}

  bool operator==(const IndexedRootPredicate& irp) const
  {
    return d_index == irp.d_index;
  }
}; /* struct IndexedRootPredicate */

inline std::ostream& operator<<(std::ostream& os,
                                const IndexedRootPredicate& irp) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& os,
                                const IndexedRootPredicate& irp)
{
  return os << "k=" << irp.d_index;
}

struct CVC4_PUBLIC IndexedRootPredicateHashFunction
{
  std::size_t operator()(const IndexedRootPredicate& irp) const
  {
    return irp.d_index;
  }
}; /* struct IndexedRootPredicateHashFunction */

}  // namespace CVC4

#endif