
#include "expr/node.h"
#include "expr/attribute.h"


#ifndef __CVC4__THEORY__ARITH__BASIC_H
#define __CVC4__THEORY__ARITH__BASIC_H

namespace CVC4 {
namespace theory {
namespace arith {

struct IsBasicAttrID;

typedef expr::Attribute<IsBasicAttrID, bool> IsBasic;


inline bool isBasic(TNode x){
  return x.getAttribute(IsBasic());
}

inline void makeBasic(TNode x){
  return x.setAttribute(IsBasic(), true);
}

inline void makeNonbasic(TNode x){
  return x.setAttribute(IsBasic(), false);
}

}; /* namespace arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH__BASIC_H */
