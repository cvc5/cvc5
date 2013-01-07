#include "mcsat/cnf/cnf_plugin.h"

using namespace CVC4;
using namespace mcsat;

CNFPlugin::CNFPlugin(ClauseDatabase& database, const SolverTrail& trail, SolverPluginRequest& request)
: SolverPlugin(database, trail, request)
, d_cnfStreamListener(*this)
, d_inputClauseRule(database, trail)
{
  // We want to know about any assertions
  addNotification(NOTIFY_ASSERTION);

  // We get the clauses from the cnf converter
  d_cnfStream.addOutputListener(&d_cnfStreamListener);
}

std::string CNFPlugin::toString() const  {
  return "CNF Conversion";
}

void CNFPlugin::CnfListener::newClause(LiteralVector& clause) {
  CRef cRef = d_cnfPlugin.d_inputClauseRule.apply(clause);
  // CRef can be null for clauses that are tautologies or true
  if (!cRef.isNull()) {
    d_cnfPlugin.d_convertedClauses.push_back(cRef);
  }
}

void CNFPlugin::notifyAssertion(TNode assertion) {
  // Convert the assertion
  d_cnfStream.convert(assertion, false);
}

void CNFPlugin::gcMark(std::set<Variable>& varsToKeep, std::set<CRef>& clausesToKeep) {
  // Remove any satisfied clauses
  d_trail.removeSatisfied(d_convertedClauses);
  clausesToKeep.insert(d_convertedClauses.begin(), d_convertedClauses.end());
}

void CNFPlugin::gcRelocate(const VariableGCInfo& vReloc, const ClauseRelocationInfo& cReloc) {
  cReloc.relocate(d_convertedClauses);
}
