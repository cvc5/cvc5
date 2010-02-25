#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace arith {

class TheoryArith : public TheoryImpl<TheoryArith> {
public:
  TheoryArith(context::Context* c, OutputChannel& out) :
    TheoryImpl<TheoryArith>(c, out) {
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

