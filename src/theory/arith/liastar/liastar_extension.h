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
/** A matrix of Normaliz integers, one row per vector. */
typedef std::vector<std::vector<Integer>> Matrix;
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
 *    linear sets g + H_i*N, one per module generator g of P_i, where H_i is
 *    the Hilbert basis of the recession cone of P_i.
 * 3. The star of a linear set g + H*N is
 *    {mu*g + H*l | mu >= 0, l >= 0, mu = 0 => l = 0}, and the star of a union
 *    is the sum of the stars. Fresh integer skolems for mu and l thus express
 *    y in S* in linear arithmetic.
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
  typedef context::CDHashSet<Node> NodeSet;

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
   * polarity, and send lemmas for them. For a literal with lambda
   * (lambda ((x_1 Int) ... (x_n Int)) p) and vector y = (y_1, ..., y_n),
   * where p(y) is p with x replaced by y, this
   * 1. with --arith-liastar-assume-nonnegative, sends
   *    (=> literal (and (>= y_1 0) ... (>= y_n 0))),
   * 2. sends the split lemma (or p(y) (not p(y))), so the SAT solver decides
   *    p(y). If this call has sent any lemma so far, e.g. this one, the
   *    literal is left for a later call,
   * 3. with --arith-liastar-model-value (the default), stops if p(y) is true
   *    in arithModel, since then y is in S and hence in S*,
   * 4. otherwise sends the reduction lemma (= literal (and ...)) of the class
   *    documentation, built by getCones, once per literal.
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
   * Collect the int.star-contains atoms of the facts asserted to arithmetic:
   * the atom itself for (int.star-contains ...) and for
   * (not (int.star-contains ...)).
   *
   * @param assertions the vector the atoms are appended to
   */
  void getAssertions(std::vector<Node>& assertions);

  /**
   * @param v a tuple of integer terms (v_1, ..., v_n)
   * @return a formula that holds exactly when some v_i is not 0
   */
  Node isNotZeroVector(Node v);

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
   * h_1, ..., h_k of its disjunct, the constraints are
   *   (>= mu 0), and (>= l_j 0) and (=> (= mu 0) (= l_j 0)) for each j,
   * with fresh skolems mu and l_1, ..., l_k, and finally, for each coordinate
   *   (= y_i (+ ... (* g_i mu) (* h_1i l_1) ... (* h_ki l_k) ...))
   * summing over all module generators. A disjunct without constant terms,
   * e.g. (and (>= x y) (>= y 0)), is a cone: it has no module generators,
   * and its integer points are the single linear set 0 + H*N, for which mu
   * is 1.
   *
   * @param n the int.star-contains literal
   * @param pairs the constraint systems of the disjuncts, see
   * convertQFLIAToMatrices
   * @return the nonempty cones with their disjuncts, and the constraints
   */
  std::pair<std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>,
            std::vector<Node>>
  getCones(Node n,
           const std::vector<std::pair<std::vector<std::string>, Node>>& pairs);

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
  /** The state of the theory of arithmetic */
  TheoryState& d_astate;
  /** The inference manager of the theory of arithmetic */
  InferenceManager& d_im;
  /** The number of calls to checkFullEffort */
  unsigned d_checkCounter;
  /** The callback of d_extTheory */
  ExtTheoryCallback d_extTheoryCb;
  /** Extended theory, with which the int.star-contains terms are registered */
  ExtTheory d_extTheory;
  /** Whether an int.star-contains term was preregistered in this context */
  context::CDO<bool> d_hasLiaStarTerms;
  /** The literals whose reduction lemma was sent, see checkFullEffort */
  std::vector<Node> d_processedStarTerms;

  /** Statistics for the liastar extension */
  LiaStarStatistics d_stats;

}; /* class LiaStarExtension */

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__LIASTAR_EXTENSION_H */

#endif /* CVC5_USE_NORMALIZ */