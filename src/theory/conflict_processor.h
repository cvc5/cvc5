/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Conflict processor module
 */

#include "cvc5_public.h"

#ifndef CVC5__THEORY__CONFLICT_PROCESSOR_H
#define CVC5__THEORY__CONFLICT_PROCESSOR_H

#include "expr/node.h"
#include "expr/subs.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"
#include "theory/substitutions.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

class TheoryEngine;
class Assigner;

namespace theory {

/**
 * IDEAS: Use top-level substitutions? combine with inprocess?
 * duplication under substitution?
 * infer substitutions for terms? f(t) where FV(t) not in sigma
 */
class ConflictProcessor : protected EnvObj
{
 public:
  ConflictProcessor(Env& env);
  ~ConflictProcessor() {}

  /**
   * Attempt to rewrite a lemma to a stronger one. For example, the lemma
   * (=> (= x a) (or B C)) may be replaced by (=> (= x a) B) if B[a/x] rewrites
   * to true.
   * 
   * @param lem The lemma.
   * @return A trust node for a lemma that implies lem.
   */
  TrustNode processLemma(const TrustNode& lem);

 private:
  /** Common constants */
  Node d_true;
  Node d_false;
  Node d_nullNode;
  /** Use the extended rewriter? */
  bool d_useExtRewriter;
  /** Statistics about the conflict processor */
  struct Statistics
  {
    Statistics(StatisticsRegistry& sr);
    /** Total number of lemmas */
    IntStat d_initLemmas;
    /** Total number of lemmas */
    IntStat d_lemmas;
    /** Total number of minimized lemmas */
    IntStat d_minLemmas;
  };
  Statistics d_stats;
  /**
   * Decompose lemma into a substitution and a remainder. For example, the
   * lemma (or (not (= 0 x)) (= (* x y) 0)) is decomposed as follows:
   * s = {x->0}
   * varToExp = {x -> (= 0 x)}
   * tgtLits = {(= (* x y) 0)}
   *
   * More generally, note that the lem is equivalent to
   *   (=> (and (= x_1 c_1) .... (= x_n c_n)) (and tgtLits[1] ... tgtLits[n]))
   * where s = { x_1 -> c_1, ..., x_n -> c_n }.
   *
   * @param lem The lemma.
   * @param s The substitution that can be derived from lem.
   * @param varToExp Maps variables in the domain of s to the literal that
   * explains why they are equal to the range.
   * @param tgtLits The literals that were not accounted for in the
   * substitution.
   */
  void decomposeLemma(const Node& lem,
                      SubstitutionMap& s,
                      std::map<Node, Node>& varToExp,
                      std::vector<Node>& tgtLits) const;
  /**
   * Evaluate substitution.
   * @param s The current substitution.
   * @param tgt The target formula.
   * @return The result of evaluating tgt under the substitution s.
   */
  Node evaluateSubstitution(const SubstitutionMap& s, const Node& tgt) const;
  /**
   * Evaluate substitution for a literal.
   * @param s The current substitution.
   * @param tgtLit The target literal.
   * @return The result of evaluating tgtLit under the substitution s.
   */
  Node evaluateSubstitutionLit(const SubstitutionMap& s,
                               const Node& tgtLit) const;
  /**
   * Is assignment equality? Returns true if n is an equality from which
   * a substitution can be inferred and added to s. It does not consider
   * substitutions that induce cycles or are for variables that already have
   * substitutions. For example, given current substitution s = {y->z},
   *    (= x y) returns true with x -> y.
   *    (= x (f x)) return false.
   *    (= y c) returns false.
   *    (= z (f y)) returns false.
   * @param s The current substitution.
   * @param n The literal in question.
   * @param v If this method returns true, this updates v to the variable of
   * the new substitution.
   * @param c If this method returns true, this updates c to the substitution
   * for v.
   */
  bool isAssignEq(const SubstitutionMap& s,
                  const Node& n,
                  Node& v,
                  Node& c) const;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__ASSIGNER_H */
