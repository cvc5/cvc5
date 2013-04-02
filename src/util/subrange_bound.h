/*********************                                                        */
/*! \file subrange_bound.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Tim King
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
#include "util/exception.h"

#include <limits>

namespace CVC4 {

/**
 * Representation of a subrange bound.  A bound can either exist and be
 * a finite arbitrary-precision integer, or not exist (and thus be
 * an infinite bound).  For example, the CVC language subrange [-5.._]
 * has a lower bound of -5 and an infinite upper bound.
 */
class CVC4_PUBLIC SubrangeBound {
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
  const Integer& getBound() const throw(IllegalArgumentException) {
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

  /**
   * Is this SubrangeBound "less than" another?  For two
   * SubrangeBounds that "have bounds," this is defined as expected.
   * For a finite SubrangeBound b1 and a SubrangeBounds b2 without a
   * bound, b1 < b2 (but note also that b1 > b2).  This strange
   * behavior is due to the fact that a SubrangeBound without a bound
   * is the representation for both +infinity and -infinity.
   */
  bool operator<(const SubrangeBound& b) const throw() {
    return (!hasBound() && b.hasBound()) || (hasBound() && !b.hasBound()) ||
      ( hasBound() && b.hasBound() && getBound() < b.getBound() );
  }

  /**
   * Is this SubrangeBound "less than or equal to" another?  For two
   * SubrangeBounds that "have bounds," this is defined as expected.
   * For a finite SubrangeBound b1 and a SubrangeBounds b2 without a
   * bound, b1 < b2 (but note also that b1 > b2).  This strange
   * behavior is due to the fact that a SubrangeBound without a bound
   * is the representation for both +infinity and -infinity.
   */
  bool operator<=(const SubrangeBound& b) const throw() {
    return !hasBound() || !b.hasBound() ||
      ( hasBound() && b.hasBound() && getBound() <= b.getBound() );
  }

  /**
   * Is this SubrangeBound "greater than" another?  For two
   * SubrangeBounds that "have bounds," this is defined as expected.
   * For a finite SubrangeBound b1 and a SubrangeBounds b2 without a
   * bound, b1 > b2 (but note also that b1 < b2).  This strange
   * behavior is due to the fact that a SubrangeBound without a bound
   * is the representation for both +infinity and -infinity.
   */
  bool operator>(const SubrangeBound& b) const throw() {
    return (!hasBound() && b.hasBound()) || (hasBound() && !b.hasBound()) ||
      ( hasBound() && b.hasBound() && getBound() < b.getBound() );
  }

  /**
   * Is this SubrangeBound "greater than or equal to" another?  For
   * two SubrangeBounds that "have bounds," this is defined as
   * expected.  For a finite SubrangeBound b1 and a SubrangeBounds b2
   * without a bound, b1 > b2 (but note also that b1 < b2).  This
   * strange behavior is due to the fact that a SubrangeBound without
   * a bound is the representation for both +infinity and -infinity.
   */
  bool operator>=(const SubrangeBound& b) const throw() {
    return !hasBound() || !b.hasBound() ||
      ( hasBound() && b.hasBound() && getBound() <= b.getBound() );
  }


  static SubrangeBound min(const SubrangeBound& a, const SubrangeBound& b){
    if(a.hasBound() && b.hasBound()){
      return SubrangeBound(Integer::min(a.getBound(), b.getBound()));
    }else{
      return SubrangeBound();
    }
  }

 static SubrangeBound max(const SubrangeBound& a, const SubrangeBound& b){
    if(a.hasBound() && b.hasBound()){
      return SubrangeBound(Integer::max(a.getBound(), b.getBound()));
    }else{
      return SubrangeBound();
    }
 }

};/* class SubrangeBound */

class CVC4_PUBLIC SubrangeBounds {
public:

  SubrangeBound lower;
  SubrangeBound upper;

  SubrangeBounds(const SubrangeBound& l, const SubrangeBound& u) :
    lower(l),
    upper(u) {
    CheckArgument(!l.hasBound() || !u.hasBound() ||
                  l.getBound() <= u.getBound(),
                  l, "Bad subrange bounds specified");
  }

  bool operator==(const SubrangeBounds& bounds) const {
    return lower == bounds.lower && upper == bounds.upper;
  }

  bool operator!=(const SubrangeBounds& bounds) const {
    return !(*this == bounds);
  }

  /**
   * Is this pair of SubrangeBounds "less than" (contained inside) the
   * given pair of SubrangeBounds?  Think of this as a subtype
   * relation, e.g., [0,2] < [0,3]
   */
  bool operator<(const SubrangeBounds& bounds) const {
    return (lower > bounds.lower && upper <= bounds.upper) ||
      (lower >= bounds.lower && upper < bounds.upper);
  }

  /**
   * Is this pair of SubrangeBounds "less than or equal" (contained
   * inside) the given pair of SubrangeBounds?  Think of this as a
   * subtype relation, e.g., [0,2] < [0,3]
   */
  bool operator<=(const SubrangeBounds& bounds) const {
    return lower >= bounds.lower && upper <= bounds.upper;
  }

  /**
   * Is this pair of SubrangeBounds "greater than" (does it contain)
   * the given pair of SubrangeBounds?  Think of this as a supertype
   * relation, e.g., [0,3] > [0,2]
   */
  bool operator>(const SubrangeBounds& bounds) const {
    return (lower < bounds.lower && upper >= bounds.upper) ||
      (lower <= bounds.lower && upper > bounds.upper);
  }

  /**
   * Is this pair of SubrangeBounds "greater than" (does it contain)
   * the given pair of SubrangeBounds?  Think of this as a supertype
   * relation, e.g., [0,3] > [0,2]
   */
  bool operator>=(const SubrangeBounds& bounds) const {
    return lower <= bounds.lower && upper >= bounds.upper;
  }

  /**
   * Returns true if the join of two subranges is not (- infinity, + infinity).
   */
  static bool joinIsBounded(const SubrangeBounds& a, const SubrangeBounds& b){
    return (a.lower.hasBound() && b.lower.hasBound()) ||
      (a.upper.hasBound() && b.upper.hasBound());
  }

  /**
   * Returns the join of two subranges, a and b.
   * precondition: joinIsBounded(a,b) is true
   */
  static SubrangeBounds join(const SubrangeBounds& a, const SubrangeBounds& b){
    DebugCheckArgument(joinIsBounded(a,b), a);
    SubrangeBound newLower = SubrangeBound::min(a.lower, b.lower);
    SubrangeBound newUpper = SubrangeBound::max(a.upper, b.upper);
    return SubrangeBounds(newLower, newUpper);
  }

};/* class SubrangeBounds */

struct CVC4_PUBLIC SubrangeBoundsHashFunction {
  inline size_t operator()(const SubrangeBounds& bounds) const {
    // We use Integer::hash() rather than Integer::getUnsignedLong()
    // because the latter might overflow and throw an exception
    size_t l = bounds.lower.hasBound() ? bounds.lower.getBound().hash() : std::numeric_limits<size_t>::max();
    size_t u = bounds.upper.hasBound() ? bounds.upper.getBound().hash() : std::numeric_limits<size_t>::max();
    return l + 0x9e3779b9 + (u << 6) + (u >> 2);
  }
};/* struct SubrangeBoundsHashFunction */

inline std::ostream&
operator<<(std::ostream& out, const SubrangeBound& bound) throw() CVC4_PUBLIC;

inline std::ostream&
operator<<(std::ostream& out, const SubrangeBound& bound) throw() {
  if(bound.hasBound()) {
    out << bound.getBound();
  } else {
    out << '_';
  }

  return out;
}

inline std::ostream&
operator<<(std::ostream& out, const SubrangeBounds& bounds) throw() CVC4_PUBLIC;

inline std::ostream&
operator<<(std::ostream& out, const SubrangeBounds& bounds) throw() {
  out << bounds.lower << ".." << bounds.upper;

  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__SUBRANGE_BOUND_H */
