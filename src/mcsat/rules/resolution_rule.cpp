#include "mcsat/rules/resolution_rule.h"

using namespace CVC4;
using namespace mcsat;
using namespace rules;

BooleanResolutionRule::BooleanResolutionRule(ClauseDatabase& clauseDB, const SolverTrail& trail)
: ProofRule("mcsat::resolution_rule", clauseDB, trail)
, d_stepsCount(0)
{
}

void BooleanResolutionRule::start(CRef initialClause) {
  Debug("mcsat::resolution_rule") << "BooleanResolutionRule(): starting with " << initialClause << std::endl;

  Assert(d_literals.size() == 0);

  d_stepsCount = 0;
  d_initialClause = initialClause;

  Clause& clause = initialClause.getClause();
  for (unsigned i = 0; i < clause.size(); ++ i) {
    d_literals.insert(clause[i]);
  }
}

void BooleanResolutionRule::resolve(CRef cRef, unsigned literalIndex) {
  Debug("mcsat::resolution_rule") << "BooleanResolutionRule(): resolving " << d_literals << " with " << cRef << std::endl;
  Clause& toResolve = cRef.getClause();
  Assert(literalIndex < toResolve.size());

  // Increase number of steps
  d_stepsCount ++;

  // Add all the literals and remove the one we're resolving
  for (unsigned i = 0; i < toResolve.size(); ++ i) {
    Literal l = toResolve[i];
    if (i == literalIndex) {
      d_literals.remove(~l);
    } else {
      Assert(!d_literals.contains(~l));
      d_literals.insert(l);
    }
  }

  // Make sure that empty clause is false
  if (d_literals.size() == 0) {
    Node falseNode = NodeManager::currentNM()->mkConst<bool>(false);
    Variable falseVar = VariableDatabase::getCurrentDB()->getVariable(falseNode);
    d_literals.insert(Literal(falseVar, false));
  }

  Debug("mcsat::resolution_rule") << "BooleanResolutionRule(): got " << d_literals << std::endl;
}

CRef BooleanResolutionRule::finish() {

  std::vector<Literal> literals;
  d_literals.get(literals);

  CRef result = d_stepsCount == 0 ? d_initialClause : commit(literals);

  d_literals.clear();
  d_stepsCount = 0;
  d_initialClause = CRef::null;

  return result;
}

void BooleanResolutionRule::getLiterals(std::vector<Literal>& out) {
  d_literals.get(out);
}
