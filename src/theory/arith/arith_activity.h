
#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_ACTIVITY_H
#define __CVC4__THEORY__ARITH__ARITH_ACTIVITY_H

#include "expr/node.h"
#include "expr/attribute.h"

namespace CVC4 {
namespace theory {
namespace arith {


struct ArithActivityID {};
typedef expr::Attribute<ArithActivityID, uint64_t> ArithActivity;

inline void resetActivity(TNode var){
  var.setAttribute(ArithActivity(), 0);
}
inline void initActivity(TNode var){
  resetActivity(var);
}

inline uint64_t getActivity(TNode var){
  return var.getAttribute(ArithActivity());
}

inline void increaseActivity(TNode var, uint64_t x){
  Assert(var.hasAttribute(ArithActivity()));
  uint64_t newValue = x + getActivity(var);
  var.setAttribute(ArithActivity(), newValue);
}

const static uint64_t ACTIVITY_THRESHOLD = 100;

}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */


#endif
