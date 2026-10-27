/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Extension to the theory of arithmetic for the LIA* predicate
 * int.star-contains.
 */

#ifdef CVC5_USE_NORMALIZ

#ifndef CVC5__THEORY__ARITH__LIASTAR_EXTENSION_H
#define CVC5__THEORY__ARITH__LIASTAR_EXTENSION_H

#include <map>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "expr/node.h"
#include "libnormaliz/libnormaliz.h"
#include "smt/env_obj.h"
#include "theory/arith/liastar/liastar_stats.h"
#include "theory/ext_theory.h"
#include "theory/theory.h"
#include "util/result.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class InferenceManager;
class TheoryArith;

namespace liastar {

/**
 * The integer type used by Normaliz, as in liastar_utils.h. Note this shadows
 * cvc5::internal::Integer within namespace liastar.
 */
typedef mpz_class Integer;
/** A vector of integer terms, e.g. (* 2 mu) (* 1 mu) in getCones. */
typedef std::vector<Node> Vector;
/**
 * The LIA* extension, for literals of the form
 *   (int.star-contains (lambda ((x_1 Int) ... (x_n Int)) p) y_1 ... y_n)
 * which state that y = (y_1, ..., y_n) is a sum of finitely many vectors of
 * S = {x | p(x)}, i.e. y is in the star S* of S (the empty sum is 0).
 *
 * Such a literal is reduced to linear integer arithmetic by a lemma:
 * 1. p is converted to a DNF D_1 or ... or D_m, so S is the union of the
 *    integer points of the polyhedra P_i = {x | D_i(x)}.
 * 2. Normaliz describes the integer points of each P_i as a finite union of
 *    linear sets g + H_i*N + M_i*Z, one per module generator g of P_i, where
 *    H_i is the Hilbert basis of the recession cone of P_i and M_i is a
 *    basis of its maximal subspace, which is empty unless P_i contains a
 *    line.
 * 3. The star of a linear set g + H*N + M*Z is
 *    {mu*g + H*l + M*m | mu >= 0, l >= 0, mu = 0 => (l = 0 and m = 0)}, and
 *    the star of a union is the sum of the stars. Fresh integer skolems for
 *    mu, l and m thus express y in S* in linear arithmetic.
 *
 * For example, S = {(x, y) | x >= 2 and y = 1} has the module generator
 * (2, 1) and the Hilbert basis {(1, 0)}, so the literal
 *   L = (int.star-contains (lambda ((x Int) (y Int)) (and (>= x 2) (= y 1)))
 *                          a b)
 * is reduced by the lemma
 *   (= L (and (>= mu 0) (>= l 0) (=> (= mu 0) (= l 0))
 *             (= a (+ (* 2 mu) l)) (= b mu)))
 * Here the implication excludes (1, 0) = 0*(2, 1) + 1*(1, 0), which is not a
 * sum of vectors of S.
 *
 * The skolems witness y in S* when L holds, but when L is false the lemma
 * only says that this one choice of them is not a witness. A negated L is
 * therefore also reduced by the lemma
 *   (or L (forall ((mu Int) (l Int))
 *           (not (and (>= mu 0) (>= l 0) (=> (= mu 0) (= l 0))
 *                     (= a (+ (* 2 mu) l)) (= b mu)))))
 * which the quantifier instantiation for linear arithmetic handles. For
 * example, (not L) with a = 5 and b = 2 is unsat, since (5, 2) is
 * (2, 1) + (3, 1).
 *
 * TheoryArith preregisters terms with preRegisterTerm and calls
 * checkFullEffort at full effort, once the linear solver has a model. See
 * also
 * - Levatich, M., Bjorner, N., Piskac, R., Shoham, S. (2020).
 *   Solving LIA* Using Approximations.
 *   VMCAI 2020.
 *   https://doi.org/10.1007/978-3-030-39322-9_17
 */
class LiaStarExtension : EnvObj
{
 public:
  /**
   * @param env the environment
   * @param containing the theory of arithmetic, whose facts are checked and
   * whose inference manager sends the lemmas
   */
  LiaStarExtension(Env& env, TheoryArith& containing);
  ~LiaStarExtension();
  /**
   * Register n with the extended theory if it is an int.star-contains term.
   *
   * @param n a term preregistered with the theory of arithmetic
   */
  void preRegisterTerm(TNode n);

  /**
   * Check the int.star-contains literals asserted to arithmetic, of either
   * polarity, and send lemmas for them. For a literal whose atom L has
   * lambda (lambda ((x_1 Int) ... (x_n Int)) p) and vector
   * y = (y_1, ..., y_n), where p(y) is p with x replaced by y, this
   * 1. with --arith-liastar-assume-nonnegative, sends
   *    (=> L (and (>= y_1 0) ... (>= y_n 0))),
   * 2. sends the split lemma (or p(y) (not p(y))), so the SAT solver decides
   *    p(y). If this call has sent any lemma so far, e.g. this one, the
   *    literal is left for a later call,
   * 3. with --arith-liastar-model-value (the default), stops for a positive
   *    literal if p(y) is true in arithModel, since then y is in S and hence
   *    in S*,
   * 4. otherwise sends the reduction lemma (= L (and ...)) of the class
   *    documentation, built by getCones, once per atom, and for a negative
   *    literal also the lemma (or L (forall ...)), once per atom.
   *
   * @param arithModel the model of the linear solver, which maps arithmetic
   * variables to constants, e.g. {a -> 3, b -> 1}
   * @param termSet the terms of the model, only traced
   */
  void checkFullEffort(std::map<Node, Node>& arithModel,
                       const std::set<Node>& termSet);

  /** Whether an int.star-contains term was preregistered in this context. */
  bool hasLiaStarTerms() const { return d_hasLiaStarTerms; }

 private:
  /**
   * Collect the facts asserted to arithmetic of the form
   * (int.star-contains ...) or (not (int.star-contains ...)).
   *
   * @param assertions the vector the literals are appended to
   */
  void getAssertions(std::vector<Node>& assertions);

  /**
   * Convert the body p of a lambda into one Normaliz constraint system per
   * disjunct of its DNF, see LiaStarUtils::toDNF and LiaStarUtils::getMatrices.
   * For example, the lambda
   *   (lambda ((x Int) (y Int)) (or (and (>= x 2) (= y 1)) (>= y 3)))
   * yields the pairs
   *   {"x[1] >= 2;", "x[2] = 1;"} with (and (>= x 2) (= y 1))
   *   {"x[2] >= 3;"} with (>= y 3)
   *
   * @param n a lambda (lambda ((x_1 Int) ... (x_n Int)) p) with p in LIA
   * @return one pair per disjunct: its constraints over the Normaliz
   * coordinates x[1]..x[n], together with the disjunct itself
   */
  const std::vector<std::pair<std::vector<std::string>, Node>>
  convertQFLIAToMatrices(Node n);

  /**
   * Compute with Normaliz the linear sets of each disjunct, and the
   * constraints stating that the vector y of n is in the star of their union,
   * see steps 2 and 3 above. For each module generator g, with Hilbert basis
   * and maximal subspace h_1, ..., h_k of its disjunct, see
   * getHilbertBasisWithLineality, the constraints are
   *   (>= mu 0), and (=> (= mu 0) (= l_j 0)) for each j,
   *   (>= l_j 0) for each h_j of the Hilbert basis,
   * with fresh skolems mu and l_1, ..., l_k, and finally, for each coordinate
   *   (= y_i (+ ... (* g_i mu) (* h_1i l_1) ... (* h_ki l_k) ...))
   * summing over all module generators. A disjunct without constant terms,
   * e.g. (and (>= x y) (>= y 0)), is a cone: it has no module generators,
   * and its integer points are the single linear set 0 + H*N + M*Z, for
   * which mu is 1. A disjunct without integer points, e.g.
   * (and (= x (* 2 z)) (= x (+ (* 2 w) 1))), is skipped.
   *
   * @param n the int.star-contains atom
   * @param pairs the constraint systems of the disjuncts, see
   * convertQFLIAToMatrices
   * @param skolems the vector the fresh skolems mu and l_j are appended to
   * @return the nonempty cones with their disjuncts, and the constraints
   */
  std::pair<std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>,
            std::vector<Node>>
  getCones(Node n,
           const std::vector<std::pair<std::vector<std::string>, Node>>& pairs,
           std::vector<Node>& skolems);

  /**
   * Send the reduction lemma (or atom (forall ((mu Int) ...) (not C))) of a
   * negated atom, stored in d_negatedReductions, see checkFullEffort. Does
   * nothing if C has no skolems, as the reduction lemma (= atom C) is then
   * exact.
   *
   * @param atom an int.star-contains atom that is asserted false
   * @throws LogicException if the lemma is needed but the logic has no
   * quantifiers
   */
  void sendNegatedReduction(Node atom);

  /**
   * Normaliz's getHilbertBasis() only covers the pointed part of a cone: for
   * a cone containing a line, e.g. the one of (= (+ x y) 2) whose maximal
   * subspace is spanned by (1, -1), the nonnegative combinations of its
   * Hilbert basis miss lattice points. The basis of the maximal subspace is
   * appended to complete it. A direction of the maximal subspace can be used
   * both ways, so its multiplier is unrestricted in sign. Appending m and -m
   * instead would also be correct, but gives every point infinitely many
   * representations, which the arithmetic search then has to enumerate.
   *
   * @param cone a cone whose HilbertBasis and MaximalSubspace are computed
   * @param numPointed set to the number of leading vectors that come from
   * getHilbertBasis() and so take nonnegative multipliers
   * @return the Hilbert basis followed by the basis of the maximal subspace,
   * which is just the Hilbert basis for a pointed cone
   */
  static std::vector<std::vector<Integer>> getHilbertBasisWithLineality(
      libnormaliz::Cone<Integer>& cone, size_t& numPointed);

  /**
   * Express each linear set g + H*N of the cones as a LIA formula over the
   * variables of the lambda, for the trace liastar-ext-smt only. For the
   * disjunct (and (>= x 2) (= y 1)), with g = (2, 1) and H = {(1, 0)}, it is
   *   (exists ((l1 Int)) (and (>= l1 0) (= x (+ 2 l1)) (= y 1)))
   *
   * @param n the lambda
   * @param cones the nonempty cones with their disjuncts, see getCones
   * @return one pair per module generator: the disjunct of its cone and the
   * formula
   */
  std::vector<std::pair<Node, Node>> getLia(
      Node n, std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& cones);

  /** node manager */
  NodeManager* d_nm;
  /** commonly used terms */
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
  /** The theory of arithmetic, whose asserted facts getAssertions reads */
  TheoryArith& d_arith;
  /** The inference manager of the theory of arithmetic */
  InferenceManager& d_im;
  /** The callback of d_extTheory */
  ExtTheoryCallback d_extTheoryCb;
  /** Extended theory, with which the int.star-contains terms are registered */
  ExtTheory d_extTheory;
  /** Whether an int.star-contains term was preregistered in this context */
  context::CDO<bool> d_hasLiaStarTerms;
  /**
   * Maps each atom whose reduction lemma was sent to the formula
   * (forall ((mu Int) ...) (not C)) that holds when the atom is false, or to
   * null if C has no skolems, see checkFullEffort. User-context dependent,
   * like the lemmas.
   */
  context::CDHashMap<Node, Node> d_negatedReductions;
  /** The atoms whose negated reduction lemma was sent, user-context dependent
   */
  context::CDHashSet<Node> d_negatedReductionsSent;

  /** Statistics for the liastar extension */
  LiaStarStatistics d_stats;

}; /* class LiaStarExtension */

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__LIASTAR_EXTENSION_H */

#endif /* CVC5_USE_NORMALIZ */