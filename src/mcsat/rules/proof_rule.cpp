#include "proof_rule.h"

using namespace CVC4;
using namespace CVC4::mcsat;
using namespace CVC4::mcsat::rules;

using namespace std;

CRef ProofRule::commit(LiteralVector& literals) {
  Debug("mcsat::rules") << "ProofRule<" << d_name << ">::commit(" << literals << ")" << endl;

  ++ d_applications;

  // Get the true/false constants
  TNode c_True = d_trail.getTrue();
  TNode c_False = d_trail.getFalse();

  // Sort the literals to check for duplicates and tautologies
  std::sort(literals.begin(), literals.end());

  int previous = -1;
  for (unsigned i = 0; i < literals.size(); ++ i)
  {
    // Ignore duplicate literals
    if (previous >= 0 && literals[i] == literals[previous]) {
      continue;
    }

    // Tautologies are ignored
    if (previous >= 0 && literals[i].isNegationOf(literals[previous])) {
      return CRef::null;
      break;
    }

    // Check if the literal is assigned already
    TNode value = d_trail.value(literals[i]);
    if (!value.isNull()) {
      // This value has a meaning only if it's at 0 level
      if (d_trail.decisionLevel(literals[i].getVariable()) > 0) {
        value = TNode::null();
      }
    }

    if (value == c_True) {
      // Literal is true and hence the clause too
      return CRef::null;
      break;
    }
    if (value == c_False) {
      // Literal is false and can be ignored
      continue;
    }

    // Move on
    literals[++previous] = literals[i];
  }

  // Resize to clause size
  literals.resize(previous + 1);

  if (literals.size() == 0) {
    Node falseNode = NodeManager::currentNM()->mkConst<bool>(false);
    Variable falseVar = VariableDatabase::getCurrentDB()->getVariable(falseNode);
    literals.push_back(Literal(falseVar, false));
  }

  Debug("mcsat::rules") << "ProofRule<" << d_name << ">::commit(): commiting " << literals << endl;

  return d_clauseDB.newClause(literals, d_id);
}

CRef ProofRule::commit(LiteralSet& literals) {
  LiteralVector literalVector(literals.begin(), literals.end());
  return commit(literalVector);
}

CRef ProofRule::commit(LiteralHashSet& literals) {
  LiteralVector literalVector(literals.begin(), literals.end());
  return commit(literalVector);
}

ProofRule::ProofRule(string name, ClauseDatabase& clauseDb, const SolverTrail& trail, StatisticsRegistry* registry)
: d_registry(registry)
, d_name(name)
, d_applications(name, 0)
, d_clauseDB(clauseDb)
, d_id(clauseDb.registerRule())
, d_trail(trail)
{
  d_registry->registerStat(&d_applications);  
}

ProofRule::~ProofRule() {
  d_registry->unregisterStat(&d_applications);
}
