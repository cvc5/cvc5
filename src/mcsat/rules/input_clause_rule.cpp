#include "mcsat/rules/input_clause_rule.h"

using namespace CVC4;
using namespace mcsat;
using namespace rules;

CRef InputClauseRule::apply(LiteralVector& literals) {

  // Make the clause
  return commit(literals);
}

