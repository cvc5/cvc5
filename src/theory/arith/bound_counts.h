#include "cvc4_private.h"
#pragma once

#include <stdint.h>
#include "theory/arith/arithvar.h"
#include "util/cvc4_assert.h"
#include "util/dense_map.h"

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * x = \sum_{a < 0} a_i i + \sum_{b > 0} b_j j
 *
 * AtUpperBound = {assignment(i) = lb(i)} \cup {assignment(j) = ub(j)}
 * AtLowerBound = {assignment(i) = ub(i)} \cup {assignment(j) = lb(j)}
 */
class BoundCounts {
private:
  uint32_t d_atLowerBounds;
  uint32_t d_atUpperBounds;

public:
  BoundCounts() : d_atLowerBounds(0), d_atUpperBounds(0) {}
  BoundCounts(uint32_t lbs, uint32_t ubs)
  : d_atLowerBounds(lbs), d_atUpperBounds(ubs) {}

  bool operator==(BoundCounts bc) const {
    return d_atLowerBounds == bc.d_atLowerBounds
      && d_atUpperBounds == bc.d_atUpperBounds;
  }
  bool operator!=(BoundCounts bc) const {
    return  d_atLowerBounds != bc.d_atLowerBounds
      || d_atUpperBounds != bc.d_atUpperBounds;
  }
  inline bool isZero() const{ return d_atLowerBounds == 0 && d_atUpperBounds == 0; }
  inline uint32_t atLowerBounds() const{
    return d_atLowerBounds;
  }
  inline uint32_t atUpperBounds() const{
    return d_atUpperBounds;
  }

  inline BoundCounts operator+(BoundCounts bc) const{
    return BoundCounts(d_atLowerBounds + bc.d_atLowerBounds,
                       d_atUpperBounds + bc.d_atUpperBounds);
  }

  inline BoundCounts operator-(BoundCounts bc) const {
    Assert(d_atLowerBounds >= bc.d_atLowerBounds);
    Assert(d_atUpperBounds >= bc.d_atUpperBounds);
    return BoundCounts(d_atLowerBounds - bc.d_atLowerBounds,
                       d_atUpperBounds - bc.d_atUpperBounds);
  }

  inline void addInChange(int sgn, BoundCounts before, BoundCounts after){
    Assert(before != after);
    if(sgn < 0){
      Assert(d_atUpperBounds >= before.d_atLowerBounds);
      Assert(d_atLowerBounds >= before.d_atUpperBounds);
      d_atUpperBounds += after.d_atLowerBounds - before.d_atLowerBounds;
      d_atLowerBounds += after.d_atUpperBounds - before.d_atUpperBounds;
    }else if(sgn > 0){
      Assert(d_atUpperBounds >= before.d_atUpperBounds);
      Assert(d_atLowerBounds >= before.d_atLowerBounds);
      d_atUpperBounds += after.d_atUpperBounds - before.d_atUpperBounds;
      d_atLowerBounds += after.d_atLowerBounds - before.d_atLowerBounds;
    }
  }

  inline void addInSgn(BoundCounts bc, int before, int after){
    Assert(before != after);
    Assert(!bc.isZero());

    if(before < 0){
      d_atUpperBounds -= bc.d_atLowerBounds;
      d_atLowerBounds -= bc.d_atUpperBounds;
    }else if(before > 0){
      d_atUpperBounds -= bc.d_atUpperBounds;
      d_atLowerBounds -= bc.d_atLowerBounds;
    }
    if(after < 0){
      d_atUpperBounds += bc.d_atLowerBounds;
      d_atLowerBounds += bc.d_atUpperBounds;
    }else if(after > 0){
      d_atUpperBounds += bc.d_atUpperBounds;
      d_atLowerBounds += bc.d_atLowerBounds;
    }
  }

  inline BoundCounts& operator+=(BoundCounts bc) {
    d_atUpperBounds += bc.d_atUpperBounds;
    d_atLowerBounds += bc.d_atLowerBounds;
    return *this;
  }

  inline BoundCounts& operator-=(BoundCounts bc) {
    Assert(d_atLowerBounds >= bc.d_atLowerBounds);
    Assert(d_atUpperBounds >= bc.d_atUpperBounds);
    d_atUpperBounds -= bc.d_atUpperBounds;
    d_atLowerBounds -= bc.d_atLowerBounds;

    return *this;
  }

  inline BoundCounts multiplyBySgn(int sgn) const{
    if(sgn > 0){
      return *this;
    }else if(sgn == 0){
      return BoundCounts(0,0);
    }else{
      return BoundCounts(d_atUpperBounds, d_atLowerBounds);
    }
  }
};

typedef DenseMap<BoundCounts> BoundCountingVector;

class BoundCountingLookup {
private:
  BoundCountingVector* d_bc;
public:
  BoundCountingLookup(BoundCountingVector* bc) : d_bc(bc) {}
  BoundCounts boundCounts(ArithVar v) const {
    Assert(d_bc->isKey(v));
    return (*d_bc)[v];
  }
};

inline std::ostream& operator<<(std::ostream& os, const BoundCounts& bc){
  os << "[bc " << bc.atLowerBounds() << ", "
     << bc.atUpperBounds() << "]";
  return os;
}

class BoundCountsCallback {
public:
  virtual void operator()(ArithVar v, BoundCounts bc) = 0;
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
