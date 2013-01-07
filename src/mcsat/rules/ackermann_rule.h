#pragma once

#include "mcsat/rules/proof_rule.h"
#include "mcsat/solver_trail.h"

namespace CVC4 {
namespace mcsat {
namespace rules {

/**  
 * x = y => f(x) = f(y) for given f(x) and f(y)
 */
class AckermannRule : public ProofRule {
public:
  AckermannRule(ClauseDatabase& clauseDB, const SolverTrail& trail);
  CRef apply(Variable f1, Variable f2, SolverTrail::PropagationToken& propToken, std::set<Variable>& out_vars);
};

}
}
}



