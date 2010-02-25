#include "theory/theory.h"
#include "context/context.h"

namespace CVC4 {
namespace theory {
namespace booleans {

class TheoryBool : public TheoryImpl<TheoryBool> {
public:
  TheoryBool(context::Context* c, OutputChannel& out) :
    TheoryImpl<TheoryBool>(c, out) {
  }

  void preRegisterTerm(TNode n) { Unimplemented(); }
  void registerTerm(TNode n) { Unimplemented(); }
  void check(Effort e) { Unimplemented(); }
  void propagate(Effort e) { Unimplemented(); }
  void explain(TNode n, Effort e) { Unimplemented(); }
};

}
}
}

