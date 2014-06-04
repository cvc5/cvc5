

#include "smt/logic_request.h"
#include "smt/smt_engine.h"


namespace CVC4 {

/** Widen the logic to include the given theory. */
void LogicRequest::widenLogic(theory::TheoryId id) {
  d_smt.d_logic.getUnlockedCopy();
  d_smt.d_logic = d_smt.d_logic.getUnlockedCopy();
  d_smt.d_logic.enableTheory(id);
  d_smt.d_logic.lock();
}

}/* CVC4 namespace */
