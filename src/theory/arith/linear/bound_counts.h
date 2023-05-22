/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Clark Barrett
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_private.h"
#pragma once

#include "base/check.h"
#include "theory/arith/linear/arithvar.h"
#include "util/dense_map.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

class BoundCounts {
private:
  uint32_t d_lowerBoundCount;
  uint32_t d_upperBoundCount;

public:
  BoundCounts() : d_lowerBoundCount(0), d_upperBoundCount(0) {}
  BoundCounts(uint32_t lbs, uint32_t ubs)
  : d_lowerBoundCount(lbs), d_upperBoundCount(ubs) {}

  bool operator==(BoundCounts bc) const {
    return d_lowerBoundCount == bc.d_lowerBoundCount
      && d_upperBoundCount == bc.d_upperBoundCount;
  }
  bool operator!=(BoundCounts bc) const {
    return  d_lowerBoundCount != bc.d_lowerBoundCount
      || d_upperBoundCount != bc.d_upperBoundCount;
  }
  /** This is not a total order! */
  bool operator>=(BoundCounts bc) const {
    return d_lowerBoundCount >= bc.d_lowerBoundCount &&
      d_upperBoundCount >= bc.d_upperBoundCount;
  }

  inline bool isZero() const{ return d_lowerBoundCount == 0 && d_upperBoundCount == 0; }
  inline uint32_t lowerBoundCount() const{
    return d_lowerBoundCount;
  }
  inline uint32_t upperBoundCount() const{
    return d_upperBoundCount;
  }

  inline BoundCounts operator+(BoundCounts bc) const{
    return BoundCounts(d_lowerBoundCount + bc.d_lowerBoundCount,
                       d_upperBoundCount + bc.d_upperBoundCount);
  }

  inline BoundCounts operator-(BoundCounts bc) const {
    Assert(*this >= bc);
    return BoundCounts(d_lowerBoundCount - bc.d_lowerBoundCount,
                       d_upperBoundCount - bc.d_upperBoundCount);
  }


  inline BoundCounts& operator+=(BoundCounts bc) {
    d_upperBoundCount += bc.d_upperBoundCount;
    d_lowerBoundCount += bc.d_lowerBoundCount;
    return *this;
  }

  inline BoundCounts& operator-=(BoundCounts bc) {
    Assert(d_lowerBoundCount >= bc.d_lowerBoundCount);
    Assert(d_upperBoundCount >= bc.d_upperBoundCount);
    d_upperBoundCount -= bc.d_upperBoundCount;
    d_lowerBoundCount -= bc.d_lowerBoundCount;

    return *this;
  }

  /** Based on the sign coefficient a variable is multiplied by,
   * the effects the bound counts either has no effect (sgn == 0),
   * the lower bounds and upper bounds flip (sgn < 0), or nothing (sgn >0).
   */
  inline BoundCounts multiplyBySgn(int sgn) const{
    if(sgn > 0){
      return *this;
    }else if(sgn == 0){
      return BoundCounts(0,0);
    }else{
      return BoundCounts(d_upperBoundCount, d_lowerBoundCount);
    }
  }

  inline void addInChange(int sgn, BoundCounts before, BoundCounts after){
    if(before == after){
      return;
    }else if(sgn < 0){
      Assert(d_upperBoundCount >= before.d_lowerBoundCount);
      Assert(d_lowerBoundCount >= before.d_upperBoundCount);
      d_upperBoundCount += after.d_lowerBoundCount - before.d_lowerBoundCount;
      d_lowerBoundCount += after.d_upperBoundCount - before.d_upperBoundCount;
    }else if(sgn > 0){
      Assert(d_upperBoundCount >= before.d_upperBoundCount);
      Assert(d_lowerBoundCount >= before.d_lowerBoundCount);
      d_upperBoundCount += after.d_upperBoundCount - before.d_upperBoundCount;
      d_lowerBoundCount += after.d_lowerBoundCount - before.d_lowerBoundCount;
    }
  }

  inline void addInSgn(BoundCounts bc, int before, int after){
    Assert(before != after);
    Assert(!bc.isZero());

    if(before < 0){
      d_upperBoundCount -= bc.d_lowerBoundCount;
      d_lowerBoundCount -= bc.d_upperBoundCount;
    }else if(before > 0){
      d_upperBoundCount -= bc.d_upperBoundCount;
      d_lowerBoundCount -= bc.d_lowerBoundCount;
    }
    if(after < 0){
      d_upperBoundCount += bc.d_lowerBoundCount;
      d_lowerBoundCount += bc.d_upperBoundCount;
    }else if(after > 0){
      d_upperBoundCount += bc.d_upperBoundCount;
      d_lowerBoundCount += bc.d_lowerBoundCount;
    }
  }
};

class BoundsInfo {
private:

  /**
   * x = \sum_{a < 0} a_i i + \sum_{b > 0} b_j j
   *
   * AtUpperBound = {assignment(i) = lb(i)} \cup {assignment(j) = ub(j)}
   * AtLowerBound = {assignment(i) = ub(i)} \cup {assignment(j) = lb(j)}
   */
  BoundCounts d_atBounds;

  /** This is for counting how many upper and lower bounds a row has. */
  BoundCounts d_hasBounds;

public:
  BoundsInfo() : d_atBounds(), d_hasBounds() {}
  BoundsInfo(BoundCounts atBounds, BoundCounts hasBounds)
    : d_atBounds(atBounds), d_hasBounds(hasBounds) {}

  BoundCounts atBounds() const { return d_atBounds; }
  BoundCounts hasBounds() const { return d_hasBounds; }

  /** This corresponds to adding in another variable to the row. */
  inline BoundsInfo operator+(const BoundsInfo& bc) const{
    return BoundsInfo(d_atBounds + bc.d_atBounds,
                      d_hasBounds + bc.d_hasBounds);
  }
  /** This corresponds to removing a variable from the row. */
  inline BoundsInfo operator-(const BoundsInfo& bc) const {
    Assert(*this >= bc);
    return BoundsInfo(d_atBounds - bc.d_atBounds,
                      d_hasBounds - bc.d_hasBounds);
  }

  inline BoundsInfo& operator+=(const BoundsInfo& bc) {
    d_atBounds += bc.d_atBounds;
    d_hasBounds += bc.d_hasBounds;
    return (*this);
  }

  /** Based on the sign coefficient a variable is multiplied by,
   * the effects the bound counts either has no effect (sgn == 0),
   * the lower bounds and upper bounds flip (sgn < 0), or nothing (sgn >0).
   */
  inline BoundsInfo multiplyBySgn(int sgn) const{
    return BoundsInfo(d_atBounds.multiplyBySgn(sgn), d_hasBounds.multiplyBySgn(sgn));
  }

  bool operator==(const BoundsInfo& other) const{
    return d_atBounds == other.d_atBounds && d_hasBounds == other.d_hasBounds;
  }
  bool operator!=(const BoundsInfo& other) const{
    return !(*this == other);
  }
  /** This is not a total order! */
  bool operator>=(const BoundsInfo& other) const{
    return d_atBounds >= other.d_atBounds && d_hasBounds >= other.d_hasBounds;
  }
  void addInChange(int sgn, const BoundsInfo& before, const BoundsInfo& after){
    addInAtBoundChange(sgn, before.d_atBounds, after.d_atBounds);
    addInHasBoundChange(sgn, before.d_hasBounds, after.d_hasBounds);
  }
  void addInAtBoundChange(int sgn, BoundCounts before, BoundCounts after){
    d_atBounds.addInChange(sgn, before, after);
  }
  void addInHasBoundChange(int sgn, BoundCounts before, BoundCounts after){
    d_hasBounds.addInChange(sgn, before, after);
  }

  inline void addInSgn(const BoundsInfo& bc, int before, int after){
    if(!bc.d_atBounds.isZero()){ d_atBounds.addInSgn(bc.d_atBounds, before, after);}
    if(!bc.d_hasBounds.isZero()){ d_hasBounds.addInSgn(bc.d_hasBounds, before, after);}
  }
};

/** This is intended to map each row to its relevant bound information. */
typedef DenseMap<BoundsInfo> BoundInfoMap;

inline std::ostream& operator<<(std::ostream& os, const BoundCounts& bc){
  os << "[bc " << bc.lowerBoundCount() << ", " << bc.upperBoundCount() << "]";
  return os;
}

inline std::ostream& operator<<(std::ostream& os, const BoundsInfo& inf){
  os << "[bi : @ " << inf.atBounds() << ", " << inf.hasBounds() << "]";
  return os;
}
class BoundUpdateCallback {
public:
  virtual ~BoundUpdateCallback() {}
  virtual void operator()(ArithVar v, const BoundsInfo&  up) = 0;
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
