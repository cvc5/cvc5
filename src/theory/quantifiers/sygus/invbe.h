/*********************                                                        */
/*! \file inv_synth.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief class for specialized approaches for invariant synthesis
 **/
#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS__INVBE_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS__INVBE_H

#include <map>
#include <string>
#include <vector>

#include "theory/quantifiers/sygus/sygus_module.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Synthesizes invariants in a "by-examples" approach
 *
 * Successively performs strengthening and weakining of candidate invariants
 * based on counterexamples produced while verifying that a candidate invariant
 * satisfies the constraints.
 *
 * Strengthening occurs when a candidate is not strong enough to rule out states
 * whose next state, after a transition step, violates the invariant. Weakining
 * occurs when a candidate is stronger than the precondition. To ensure that a
 * candidate is never weaker than the postcondition, the first candidate is
 * always the postcondition.
 *
 * The crucial insight is to use synthesis only to produce atomic expressions to
 * separate cases in which the invariant should hold to cases it should not,
 * with the boolean structure of the invariant being derived afterwards when it
 * is guaranteed to succeed with an algorithm that favors small CNFs.
 *
 * This approach is inspired by Padhi et al. PLDI 2016
 */
class InvBE : public SygusModule
{
 public:
  InvBE(QuantifiersEngine* qe, CegConjecture* p)
      : SygusModule(qe, p), d_tds(qe->getTermDatabaseSygus())
  {
  }
  ~InvBE() {}
  /** initialize this class
   *
   * If n can be broken into an inductive invariant synthesis problem, i.e. some
   * processed form equisatisfiable to
   *
   * exists Inv. forall xx'.     Pre(x) => Inv(x)
   *                         &&  Inv(x) && Trans(x, x') => Inv(x')
   *                         &&  Inv(x) => Post(x)
   *
   * then this module takes onwership of the conjecture. The module assumes
   * there is only one function to synthesize: the invariant.
   *
   * This function may add lemmas to the vector lemmas to restrict the
   * enumeration of expressions used when building candidate invariants. In
   * particular, if the grammar contains boolean operators these will be removed
   * from the enumeration since boolean combinations or theory expressions will
   * be done in a different way (see ...). */
  virtual void initialize(Node n,
                          const std::vector<Node>& candidates,
                          std::vector<Node>& lemmas) override;
  /** adds the candidate itself to enums */
  virtual void getTermList(const std::vector<Node>& candidates,
                           std::vector<Node>& enums) override;
  /** Tries to build new candidate invariant with new enumerated expresion
   *
   * This module keeps sets of points which are used to guide invariant
   * synthesis. A point is a valuation to the state variables of the transition
   * system. Points are organized in three categories:
   *
   *     good - points on which invariant must always hold
   *            true -> I[p]
   *
   *      bad - points on which invariant can never hold
   *            I[p] -> false
   *
   * relative - pairs of points for which whenever invariant holds in the
   *            first point it cannot hold in the second
   *            I[p1] -> I[p2]
   *
   * Valid candidate invariants are those which hold in all good points and in
   * no bad ones, while respecting the relative points. Such a candidate can be
   * built if we can derive atomic expressions (denominated "features") which
   * separate the points. Let a feture vector be a vector of the values of the
   * current features on a point. We associate each point to a feature vector
   * and are guaranteed to be able to build a candidate with the current
   * features when no conflict exists between the vectors. A conflict occurs in
   * two cases:
   *
   * 1) a good and a bad point have the same feature vector
   * 2) the first point of a relative pair has the same feature vector of a
   * good point and the second point has the same vector of a bad point
   *
   * If there is a conflict, this function returns false and waits for a new
   * feature to try to solve the conflicts.
   *
   * Once points can be separated without conflicts, a CNF is built (not using
   * synthesis) with the features, thus yielding the candidate invariant. */
  virtual bool constructCandidates(const std::vector<Node>& enums,
                                   const std::vector<Node>& enum_values,
                                   const std::vector<Node>& candidates,
                                   std::vector<Node>& candidate_values,
                                   std::vector<Node>& lems) override;

  /** Performs conflict analysis to obtain refinement points
   *
   * The conjecture being tested with our candidate has (some equivalent of) the
   * form
   *
   * exists J.forall xx'.   Pre(x) => J(x) && Post(x)
   *                     && J(x) && Post(x) && Trans(x, x') => J(x') && Post(x')
   *                     && J(x) && Post(x) => Post(x)
   *
   * since we are trying to build a J such that we can yield an invariant of the
   * form J(x) && Post(x).
   *
   * When the test of the conjecture fails we obtain values t and t' (for x and
   * x') as counterexamples, and consider three cases:
   *
   * 1) The invariant must be weakened (i.e. the first conjuct fails)
   * 2) The invariant must be strengthned (i.e. the second conjuct fails)
   *    2.1) if Post(t) && Trans(t, t') => Post(t') does not hold, then this
   *    counterexample is indepedent of our candidate: no matter the invariant,
   *    it must *never* hold on t.
   *    2.2) otherwise J(t) => J(t') does not hold, then this counterexample
   *    depends on the candidate
   *
   * Good points are derived from t in case (1) and bad points from t in case
   * (2.1). Relative points compose a pair with [t, t'], from case (2.2).
   *
   * Conflict analysis is complicated since the conjecture generally does not
   * have the above form, since it may have been rewritten and x' may be a
   * function of x.
   *
   * This function does not modify lems since it does not require solutions to
   * be blocked externally */
  virtual void registerRefinementLemma(const std::vector<Node>& vars,
                                       Node lem,
                                       std::vector<Node>& lems) override;
 private:
  /** sygus term database of d_qe */
  TermDbSygus * d_tds;
  /** Currently synthesized atomic expressions to separate points */
  std::vector<Node> d_features;
  /** Alias for type of points */
  using IPoint = std::vector<Node>;
  /** Good points */
  std::vector<IPoint> d_good;
  /** Feature vectors of good points */
  std::map<IPoint, std::vector<bool>> d_good_vectors;
  /** Bad points */
  std::vector<IPoint> d_bad;
  /** Feature vectors of bad points */
  std::map<IPoint, std::vector<bool>> d_bad_vectors;
  /** Relative points */
  std::vector<std::pair<IPoint, IPoint>> d_relative;
  /** Feature vectors of antecedents of relative points */
  std::map<IPoint, std::vector<bool>> d_rel_ant_vectors;
  /** Feature vectors of consequent of relative points */
  std::map<IPoint, std::vector<bool>> d_rel_cons_vectors;
  /** builds a CNF to separate good and bad valuations
   *
   * Applies a PAC (probably approximately correct) algorithm that tries to
   * build CNFs of increasing size such that all valuations in "good" hold and
   * all in "bad" do not. */
  Node buildCNF(std::vector<IPoint> good, std::vector<IPoint> bad);

}; /* class InvBE */

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
