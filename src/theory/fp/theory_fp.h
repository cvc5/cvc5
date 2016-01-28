#include "cvc4_private.h"

#ifndef __CVC4__THEORY__FP__THEORY_FP_H
#define __CVC4__THEORY__FP__THEORY_FP_H

#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace fp {

class TheoryFp : public Theory {
public:

  /** Constructs a new instance of TheoryFp w.r.t. the provided contexts. */
  TheoryFp(context::Context* c,
           context::UserContext* u,
           OutputChannel& out,
           Valuation valuation,
           const LogicInfo& logicInfo);

  Node expandDefinition(LogicRequest &, Node node);

  void check(Effort);

  std::string identify() const {
    return "THEORY_FP";
  }

};/* class TheoryFp */

}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__FP__THEORY_FP_H */
