
#ifndef __CVC4__THEORY__ARITH__NORMAL_H
#define __CVC4__THEORY__ARITH__NORMAL_H

namespace CVC4 {
namespace theory {
namespace arith {

struct IsNormalAttrID;

typedef expr::Attribute<IsNormalAttrID, bool> IsNormal;


inline bool isNormalized(TNode x){
  return x.hasAttribute(IsNormal());
}

struct NormalFormAttrID;

typedef expr::Attribute<IsNormalAttrID, Node> NormalForm;



}; /* namespace arith */
}; /* namespace theory */
}; /* namespace CVC4 */


#endif /* __CVC4__THEORY__ARITH__NORMAL_H */
