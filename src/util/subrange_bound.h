/*********************                                                        */
/*! \file subrange_bound.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Representation of subrange bounds
 **
 ** Simple class to represent a subrange bound, either infinite
 ** (no bound) or finite (an arbitrary precision integer).
 **/

#include "cvc4_public.h"

#ifndef __CVC4__SUBRANGE_BOUND_H
#define __CVC4__SUBRANGE_BOUND_H

#include "util/integer.h"
#include "util/Assert.h"

namespace CVC4 {

/**
 * Representation of a subrange bound.  A bound can either exist and be
 * a finite arbitrary-precision integer, or not exist (and thus be
 * an infinite bound).  For example, the CVC language subrange [-5.._]
 * has a lower bound of -5 and an infinite upper bound.
 */
class SubrangeBound {
  bool d_nobound;
  Integer d_bound;

public:

  /** Construct an infinite SubrangeBound. */
  SubrangeBound() throw() :
    d_nobound(true),
    d_bound() {
  }

  /** Construct a finite SubrangeBound. */
  SubrangeBound(const Integer& i) throw() :
    d_nobound(false),
    d_bound(i) {
  }

  ~SubrangeBound() throw() {
  }

  /** Get the finite SubrangeBound, failing an assertion if infinite. */
  Integer getBound() const throw(IllegalArgumentException) {
    CheckArgument(!d_nobound, this, "SubrangeBound is infinite");
    return d_bound;
  }

  /** Returns true iff this is a finite SubrangeBound. */
  bool hasBound() const throw() {
    return !d_nobound;
  }

  /** Test two SubrangeBounds for equality. */
  bool operator==(const SubrangeBound& b) const throw() {
    return hasBound() == b.hasBound() &&
      (!hasBound() || getBound() == b.getBound());
  }

  /** Test two SubrangeBounds for disequality. */
  bool operator!=(const SubrangeBound& b) const throw() {
    return !(*this == b);
  }

};/* class SubrangeBound */

inline std::ostream&
operator<<(std::ostream& out, const SubrangeBound& bound) throw() {
  if(bound.hasBound()) {
    out << bound.getBound();
  } else {
    out << '_';
  }

  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__SUBRANGE_BOUND_H */
