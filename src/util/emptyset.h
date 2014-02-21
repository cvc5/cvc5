
#include "cvc4_public.h"

#pragma once

namespace CVC4 {
  // messy; Expr needs ArrayStoreAll (because it's the payload of a
  // CONSTANT-kinded expression), and ArrayStoreAll needs Expr.
  class CVC4_PUBLIC EmptySet;
}/* CVC4 namespace */

#include "expr/expr.h"
#include "expr/type.h"
#include <iostream>

namespace CVC4 {

class CVC4_PUBLIC EmptySet {

  const SetType d_type;

public:

  EmptySet() { }		/* Null typed */
  EmptySet(SetType t):d_type(t) { }


  ~EmptySet() throw() {
  }

  SetType getType() const { return d_type; }

  bool operator==(const EmptySet& asa) const throw() {
    return d_type == asa.d_type;
  }
  bool operator!=(const EmptySet& asa) const throw() {
    return !(*this == asa);
  }

  bool operator<(const EmptySet& asa) const throw() {
    return d_type < asa.d_type;
  }
  bool operator<=(const EmptySet& asa) const throw() {
    return d_type <= asa.d_type;
  }
  bool operator>(const EmptySet& asa) const throw() {
    return !(*this <= asa);
  }
  bool operator>=(const EmptySet& asa) const throw() {
    return !(*this < asa);
  }


};/* class EmptySet */

std::ostream& operator<<(std::ostream& out, const EmptySet& asa) CVC4_PUBLIC;

struct CVC4_PUBLIC EmptySetHashFunction {
  inline size_t operator()(const EmptySet& asa) const {
    return TypeHashFunction()(asa.getType());
  }
};/* struct EmptysetHashFunction */


}
