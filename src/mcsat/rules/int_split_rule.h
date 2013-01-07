#pragma once

#include "mcsat/rules/proof_rule.h"
#include "mcsat/solver_trail.h"

namespace CVC4 {
namespace mcsat {
namespace rules {

/**  
 * Simple integer split rule. Given a variable with a non value r in the current
 * state that the given integer variable x can not be r.
 */
class IntSplitRule : public ProofRule {
public:
  IntSplitRule(ClauseDatabase& clauseDB, const SolverTrail& trail);
  CRef split(Variable x, SolverTrail::PropagationToken& propToken);
};

}
}
}



