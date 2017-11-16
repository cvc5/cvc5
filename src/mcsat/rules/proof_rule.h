#pragma once

#include "cvc4_private.h"

#include <string>
#include <vector>

#include "mcsat/clause/clause_db.h"
#include "mcsat/solver_trail.h"

#include "util/statistics_registry.h"

namespace CVC4 {
namespace mcsat {
namespace rules {

/**
 * A proof rule encapsulates the procedural part of the deduction process. It
 * should be lightweight, created once, so that the compiler can optimize it's usage.
 * Proof rules are the only entities allowed to create clauses.
 */
class ProofRule {
private:
  StatisticsRegistry* d_registry;
  /** Descriptive name of the proof rule */
  std::string d_name;
  /** Statistic for number of applications */
  IntStat d_applications;
  /** Clause database this rule is using */
  ClauseDatabase& d_clauseDB;
  /** Id of the rule with the clause database */
  size_t d_id;

protected:

  /** The trail this rule is using */
  const SolverTrail& d_trail;

  /**
   * Construct the rule with the given name.
   * @param name the name of the rule (for use in statistics)
   * @param clauseDB the database the rule will output to
   */
  ProofRule(std::string name, ClauseDatabase& clauseDB, const SolverTrail& trail, StatisticsRegistry* registry);
  /** Commit the result of the proof rule */
  CRef commit(LiteralVector& literals);
  /** Commit the result of the proof rule */
  CRef commit(LiteralSet& literals);
  /** Commit the result of the proof rule */
  CRef commit(LiteralHashSet& literals);

public:

  /** Virtual destructor */
  virtual ~ProofRule();
  /** Get the id of this rule */
  size_t getRuleId() const {
    return d_id;
  }
};

}
}
}



