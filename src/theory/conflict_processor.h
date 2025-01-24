/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
 * A utility for inferring when a theory lemma or conflict can be strengthened
 * based on substitution + rewriting.
 */
class ConflictProcessor : protected EnvObj
{
 public:
  /**
   * The constructor for this class.
   * @param env The environment.
   * @param useExtRewriter Whether we use the extended rewriter when evaluating substitutions below.
   */
  ConflictProcessor(Env& env, bool useExtRewriter = false);
  ~ConflictProcessor() {}

  /**
   * Attempt to rewrite a lemma to a stronger one. For example, the lemma
   * (=> (= x a) (or B C)) may be replaced by (=> (= x a) B) if B[a/x] rewrites
   * to true. We also may drop literals that rewrite to the same this under this
   * substitution, or drop equalities from the lemma that are determined to be
   * irrelevant based on this reasoning.
   * This method also may minimize the antecedant corresponding to a
   * substituion, e.g. (=> (and (= x a) (= y b)) B) may be replaced by
   * (=> (= x a) B) if B[a/x] rewrites to true.
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
    /** Total number of lemmas given to this module */
    IntStat d_initLemmas;
    /** Total number of lemmas for which we were able to decompose */
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
   *   (=> (and (= x_1 c_1) .... (= x_n c_n)) (or tgtLits[1] ... tgtLits[n]))
   * where s = { x_1 -> c_1, ..., x_n -> c_n }.
   *
   * Any lemma that can be decomposed is a possible target for minimization,
   * where we can recognize spurious or redundant literals, or spurious
   * equalities in the substitution.
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
   * Evaluate substitution, which returns the result applying s to tgt and
   * applying extended rewriting. If this is not equal to constant Boolean,
   * we return the null node. The formula tgt may be an AND/OR, which we
   * optimize for in this method.
   * @param s The current substitution.
   * @param tgt The target formula.
   * @return The result of evaluating tgt under the substitution s.
   */
  Node evaluateSubstitution(const SubstitutionMap& s, const Node& tgt) const;
  /**
   * Evaluate substitution for a literal. This is the same as the above method
   * but tgtLit is guaranteed to be a theory literal.
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
   *    (= y 0) returns false, since y is already bound.
   *    (= z (f y)) returns false, since this would result in a cycle.
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
