/*********************                                                        */
/*! \file indexed_root_predicate.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utils for indexed root predicates.
 **
 ** Some utils for indexed root predicates.
 **/

#include "cvc4_public.h"

#ifndef CVC4__UTIL__INDEXED_ROOT_PREDICATE_H
#define CVC4__UTIL__INDEXED_ROOT_PREDICATE_H

namespace CVC4 {

/**
 * The structure representing a root predicate.
 */
struct CVC4_PUBLIC IndexedRootPredicate
{
  /** The index of the root */
  std::uint64_t d_index;

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