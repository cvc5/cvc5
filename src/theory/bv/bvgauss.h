#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__BV_GAUSS_ELIM_H
#define __CVC4__THEORY__BV__BV_GAUSS_ELIM_H

#include "expr/node.h"
#include "util/bitvector.h"
#include <vector>
#include <unordered_map>

namespace CVC4 {
namespace theory {
namespace bv {

class BVGaussElim
{
  static void gaussElimRewrite (std::vector<Node> & assertionsToPreprocess);

  private:

  enum class Result { UNIQUE, PARTIAL, NONE };

  static Result gaussElimRewriteForUrem (
      std::vector< TNode > & equations,
      std::unordered_map< Node, Node, NodeHashFunction > & res);

  static Result gaussElim (
      Integer prime,
      std::vector< Integer > & rhs,
      std::vector< std::vector< Integer >> & lhs,
      std::vector< Integer > & resrhs,
      std::vector< std::vector< Integer >> & reslhs);
};

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif

