#pragma once

#include "mcsat/rules/proof_rule.h"
#include "mcsat/fm/linear_constraint.h"
#include "mcsat/solver_trail.h"

namespace CVC4 {
namespace mcsat {
namespace rules {

/**  
 * For regural assertions of the form (l <= x) and (x <= u) the resolution is simple.
 * If the conflict is due to v(l) > v(u) in the current model then 
 *
 * A1 = (l <= x)
 * A2 = (x <= u)
 * C  = (l <= u)
 *
 *  ----------- (FM)
 *  A1, A2 |- C
 *
 * The explanatino will be (~A1 or ~A2 or C), since C is false. The FM1 rule can 
 * be applied to eliminate successive variables if the resolvent implies a 
 * conflicting bound on the new top variable. 
 * 
 * The rule above, with it's succesive variant is available through the start, 
 * resolve and finish methods.
 *
 * The resulting clause should propagate (conflict, or explanation of a propagation)
 */
class FourierMotzkinRule : public ProofRule {

  /** The set of assumptions */
  std::set<Literal> d_assumptions;

  /** Count of false literals */
  unsigned d_trueCount;

  /** Resolvent */
  fm::LinearConstraint d_resolvent;

  /**
   * The FM rule (with cases for = and >=)
   *
   *    c1: |a| x + t > 0     c2: -|b| x + t > 0
   *    ----------------------------------------
   *                c1: |b|t + |a| t > 0
   *
   * The result goes into c1.
   */
  static void resolve(Variable x, fm::LinearConstraint& c1, fm::LinearConstraint& c2);

  friend class FourierMotzkinRuleDiseq;

public:

  /** Create a new Fourier-Motzkin resolution */
  FourierMotzkinRule(ClauseDatabase& clauseDB, const SolverTrail& trail);

  /** Start the resolution */
  void start(Literal ineq);

  /** Resolve with given inequality over the given variable. */
  void resolve(Variable var, Literal ineq);

  /** Returns the current resolvent */
  const fm::LinearConstraint& getCurrentResolvent() const;
  
  /**
   * Finish the derivation. We need the prop token, since the newly created literal will evaluate at lower level.
   */
  CRef finish(SolverTrail::PropagationToken& propToken);
};

/**
 * To resolve a conflict that is due to v(l) == v(u) and, in addition, a literal
 *
 * D = (x != t)
 *
 * with v(t) = v(l), the derivation is the following FM-D
 *
 * --------------------- (!= split)    ---------------------- (FM)
 * D |- (x < t), (t < x)               A1, (x < t) |- (l < t)
 * ---------------------------------------------------------- (Cut x < t)     ---------------------- (FM)
 *                    A1, D |- (t < x), (l < t)                               A2, (t < x) |- (t < u)
 * ------------------------------------------------------------------------------------------------- (Cut t < x)
 *                                          A1, A2, D |- (t < u), (l < t)
 *
 * Or, in conclusion, the clause is (~A1 or ~A2 or ~D or (t < u) or (l < t)).
 * This derivation is available through the resolveDisequality method.
 */
class FourierMotzkinRuleDiseq : public ProofRule {

public:

  FourierMotzkinRuleDiseq(ClauseDatabase& clauseDB, const SolverTrail& trail);

  /**
   * Do the disequality derivation.
   */
  CRef resolveDisequality(Variable var, Literal A1, Literal A2, Literal D, SolverTrail::PropagationToken& propToken);


};

}
}
}



