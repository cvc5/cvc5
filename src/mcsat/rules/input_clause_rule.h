#pragma once

#include "mcsat/rules/proof_rule.h"

namespace CVC4 {
namespace mcsat {
namespace rules {

/**
 * Rule for adding input clauses preprocessed wrt the current trail. Can be applied
 * to many clauses.
 */
class InputClauseRule : public ProofRule {
public:
  InputClauseRule(ClauseDatabase& clauseDB, const SolverTrail& trail)
  : ProofRule("mcsat::input_clause_rule", clauseDB, trail) {}

  /** Simplify and add the clause to the database */
  CRef apply(LiteralVector& literals);
};

}
}
}
