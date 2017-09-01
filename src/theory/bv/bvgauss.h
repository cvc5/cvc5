#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__BV_GAUSS_ELIM_H
#define __CVC4__THEORY__BV__BV_GAUSS_ELIM_H

#include "expr/node.h"
#include "util/bitvector.h"
#include <vector>

bool gaussElim (CVC4::Integer prime,
                std::vector< CVC4::Integer > & rhs,
                std::vector< std::vector< CVC4::Integer >> & lhs,
                std::vector< CVC4::Integer > & res);

namespace CVC4 {
namespace theory {
namespace bv {

class BVGaussElim {
  //static void gaussElimRewrite (std::vector<Node> & assertionsToPreprocess);
};

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif

