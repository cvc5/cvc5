#pragma once

#include <iostream>

#include "mcsat/clause/literal.h"

namespace CVC4 {
namespace mcsat {

/** Bound information */
struct BoundInfo {
  /** The value of the bound */
  Rational value;
  /** Is the bound strict (<,>) */
  bool strict;
  /** What is the reason for this bound */
  Literal reason;

  BoundInfo()
  : strict(false) {}

  BoundInfo(Rational value, bool strict, Literal reason = Literal())
  : value(value), strict(strict), reason(reason) {}

  /**
   * 1: better
   * 0: same
   * -1: worse
   */
  int improvesLowerBound(const BoundInfo& other) const {
    // x > value is better than x > other.value
    // if value > other.value or they are equal but this one
    // is strict
    int cmp = value.cmp(other.value);
    if (cmp == 0) {
      if (strict == other.strict) {
        return 0;
      } else {
        return strict ? 1 : -1;
      }
    } else {
      return cmp > 0 ? 1 : -1;
    }
  }

  int improvesUpperBound(const BoundInfo& other) const {
    // x < value is better than x < other.value
    // if value < other.value or they are equal but this one
    // is strict
    int cmp = value.cmp(other.value);
    if (cmp == 0) {
      if (strict == other.strict) {
        return 0;
      } else {
        return strict ? 1 : -1;
      }
    } else {
      return cmp < 0 ? 1 : -1;
    }
  }

  static bool inConflict(const BoundInfo& lower, const BoundInfo& upper) {
    // x > a and x < b are in conflict 
    // if a > b or they are equal but one is strict
    int cmp = lower.value.cmp(upper.value);
    return (cmp > 0 || (cmp == 0 && (lower.strict || upper.strict)));
  }

  void toStream(std::ostream& out) const {
    out << "[" << value << (strict ? "" : "=") << "]";
  }
};

inline std::ostream& operator << (std::ostream& out, const BoundInfo& info) {
  info.toStream(out);
  return out;
}

}
}
