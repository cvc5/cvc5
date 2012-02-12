#include "cvc4_private.h"

#ifndef __CVC4__THEORY__$id__THEORY_$id_H
#define __CVC4__THEORY__$id__THEORY_$id_H

#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace $dir {

class Theory$camel : public Theory {
public:

  /** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
  Theory$camel(context::Context* c,
               context::UserContext* u,
               OutputChannel& out,
               Valuation valuation);

  void check(Effort);

  std::string identify() const {
    return "THEORY_$id";
  }

};/* class Theory$camel */

}/* CVC4::theory::$dir namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__$id__THEORY_$id_H */
