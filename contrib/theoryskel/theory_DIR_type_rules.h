#include "cvc4_private.h"

#ifndef __CVC4__THEORY__$id__THEORY_$id_TYPE_RULES_H
#define __CVC4__THEORY__$id__THEORY_$id_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace $dir {

class $camelTypeRule {
public:

  /**
   * Compute the type for (and optionally typecheck) a term belonging
   * to the theory of $dir.
   *
   * @param check if true, the node's type should be checked as well
   * as computed.
   */
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check)
    throw (TypeCheckingExceptionPrivate) {

    // TODO: implement me!
    Unimplemented();

  }

};/* class $camelTypeRule */

}/* CVC4::theory::$dir namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__$id__THEORY_$id_TYPE_RULES_H */
