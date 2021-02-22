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
 * The structure representing the index of a root predicate.
 * An indexed root predicate has the form
 *   IRP_k(x ~ 0, p)
 * where k is a positive integer (d_index), x is a real variable,
 * ~ an arithmetic relation symbol and p a (possibly multivariate polynomial).
 * The evaluation of the predicate is obtained by comparing the k'th root of p
 * (as polynomial in x) to the value of x according to the relation symbol ~.
 * Note that p may be multivariate: in this case we can only evaluate with
 * respect to a (partial) variable assignment, that (at least) contains values
 * for all variables from p except x.
 *
 * Some examples:
 *  IRP_1(x > 0, x)  <=>  x > 0
 *  IRP_1(x < 0, x*x-1)  <=>  x < -1
 *  IRP_2(x < 0, x*x-1)  <=>  x < 1
 *  IRP_1(x = 0, x*x-2)  <=>  x = -sqrt(2)
 *  IRP_1(x = 0, x*x-y), y=3  <=>  x = -sqrt(3)
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