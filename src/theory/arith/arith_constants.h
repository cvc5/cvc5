

#include "expr/node.h"
#include "expr/node_manager.h"
#include "util/rational.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_CONSTANTS_H
#define __CVC4__THEORY__ARITH__ARITH_CONSTANTS_H

namespace CVC4 {
namespace theory {
namespace arith {

class ArithConstants{
public:
  Rational d_ZERO;
  Rational d_ONE;
  Rational d_NEGATIVE_ONE;

  Node d_ZERO_NODE;
  Node d_ONE_NODE;
  Node d_NEGATIVE_ONE_NODE;

  ArithConstants(NodeManager* nm) :
    d_ZERO(0,1),
    d_ONE(1,1),
    d_NEGATIVE_ONE(-1,1),
    d_ZERO_NODE(nm->mkConst(d_ZERO)),
    d_ONE_NODE(nm->mkConst(d_ONE)),
    d_NEGATIVE_ONE_NODE(nm->mkConst(d_NEGATIVE_ONE))
  {}
};

}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH_ARITH_CONSTANTS_H */
