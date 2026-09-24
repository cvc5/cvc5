/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solver for the theory of bags.
 */

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "cvc5_private.h"
#include "smt/env_obj.h"

#ifndef CVC5__THEORY__BAG__SOLVER_H
#define CVC5__THEORY__BAG__SOLVER_H

#include "theory/bags/inference_generator.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

class InferenceManager;
class SolverState;
class TermRegistry;

/** The solver for the theory of bags
 *
 */
class BagSolver : protected EnvObj
{
 public:
  BagSolver(Env& env, SolverState& s, InferenceManager& im);
  ~BagSolver();

  /**
   * apply inference rules for basic bag operators without quantifiers:
   * BAG_MAKE, BAG_UNION_DISJOINT, BAG_UNION_MAX, BAG_INTER_MIN,
   * BAG_DIFFERENCE_SUBTRACT, BAG_DIFFERENCE_REMOVE, BAG_SETOF
   */
  void checkBasicOperations();

  /**
   * BagsToLiastar: translate the bag constraints of the current context into
   * one liastar star-contains atom. This is the four step translation of
   * Figure 4 from [LBPS20], whose steps are referred to below by the numbers
   * they have there.
   *
   * Steps 1 and 2 are taken care of by cvc5:
   * - Flattening (step 2) is not needed, since cvc5 terms are hash consed.
   *   Every bag term is the name of itself, so the defining equation
   *   (= M_0 (op M_1 M_2)) that step 2 would introduce is the term
   *   (op M_1 M_2) itself, and its arguments are already names.
   * - Bag atoms reach this solver as literals, so the non top level atoms of
   *   step 1 are exactly the equalities in the equivalence class of false.
   *   These are eliminated by evictNegatedAtom, while the equalities in the
   *   equivalence class of true are the positive top level atoms which are
   *   translated pointwise inside the star.
   *
   * What is left is step 3 (addCardinalityVars) and step 4 (buildStar).
   *
   * This is a no op unless the bags-to-liastar option is enabled.
   *
   * Soundness. A lemma must not remove models, so what has to hold is: if the
   * input is satisfiable, then the input together with every lemma sent from
   * here is satisfiable. Take any model of the input. It gives every bag term
   * M a finite multiset [M], whose count [M](e) at an element e is a non
   * negative integer, and it is extended to the variables of the translation
   * as follows:
   * - a cardinality variable x_M denotes the cardinality |[M]|. When x_M is
   *   the skolem the context registered for the term (bag.card M) this is
   *   already its value, since that skolem is a purified form of
   *   (bag.card M). Otherwise x_M is the fresh skolem
   *   BAGS_LIASTAR_BAG_INTEGER(M), which occurs nowhere else in the problem,
   *   so it is free to be given that value. It is keyed by M alone, so the
   *   same value serves in every branch and in every check;
   * - the bound variable c_M of the body denotes [M](e), for whichever
   *   element e the summand at hand stands for.
   *
   * Every lemma sent from here holds under that one interpretation:
   * 1. the star atom. Let e_1, ..., e_m enumerate the elements that occur in
   *    any of the bags M_1, ..., M_n of the star, a finite set, and let the
   *    j-th summand be the vector ([M_1](e_j), ..., [M_n](e_j)). Summing the
   *    counts of a bag over its elements is its cardinality, so the summands
   *    add up to (|[M_1]|, ..., |[M_n]|), which is the outer vector. Each
   *    summand satisfies the body, since every conjunct of the body is a
   *    statement about a single element that holds at every element: a count
   *    is non negative; a pointwise definition is the semantics of a bag
   *    operator at an element; the conjuncts of a constructed bag hold as
   *    described in addBagMakeConstraints; and (= c_j c_k) holds because the
   *    atom (= M_j M_k) it translates is a premise of the lemma, and equal
   *    bags have equal counts at every element. So the outer vector is in the
   *    star. If there is no element at all the outer vector is zero, which
   *    every star contains.
   * 2. the lemmas of evictNegatedAtom. If [A] and [B] differ then they differ
   *    at some element e, say [A](e) > [B](e). Then [A \ B](e) > 0, so
   *    |[A \ B]| is not zero and the conjunction that the lemma negates is
   *    false.
   * 3. the cardinalities of the constructed bags. [(bag e n)] is n copies of
   *    e when n is positive and the empty bag otherwise, so its cardinality
   *    is the ite that the lemma asserts.
   * These hold under one and the same interpretation, which is what makes the
   * lemmas sound together and not only one at a time: a slot denotes the
   * cardinality of its bag, and that does not depend on the branch or on the
   * check the lemma was sent from.
   *
   * The converse is not claimed, in two ways:
   * - the star can be weaker than the bags it stands for. A bag whose kind
   *   has no pointwise translation is a slot with no definition, e.g.
   *   (bag.map f A), whose count at an element is a sum over a preimage.
   *   With this option the cardinality terms are not reduced either, so a
   *   cardinality is constrained by the star alone, and a sat answer can be
   *   spurious: the cardinality of a bag.map term is essentially free, and
   *   e.g. (= (bag.card (bag.setof A)) 1) together with
   *   (> (bag.card (bag.setof (bag.map f A))) 1) is reported sat although it
   *   is unsatisfiable;
   * - nothing reads back the decomposition the star witnesses, so the bag
   *   values of a model do not necessarily satisfy the cardinality
   *   constraints of the input.
   *
   * [LBPS20]: Solving LIA* Using Approximations, Levatich, Bjorner, Piskac
   * and Shoham, VMCAI 2020. https://doi.org/10.1007/978-3-030-39322-9_17
   */
  void checkLiastarConstraints();
  /**
   * apply inference rules for operators with quantifiers:
   * BAG_MAP
   */
  void checkQuantifiedOperations();

  /**
   * apply inference rules for BAG_MAKE terms.
   * For each term (bag x c) that is neither equal nor disequal to the empty
   * bag, we do a split using the following lemma:
   * (or
   *   (and (<  c 1) (= (bag x c) (as bag.empty (Bag E))))
   *   (and (>= c 1) (not (= (bag x c) (as bag.empty (Bag E))))
   * where (Bag E) is the type of the bag term
   * @return true if a new lemma was successfully sent.
   */
  bool checkBagMake();

 private:
  /**
   * Step 1 of BagsToLiastar for a negated bag atom, which cannot be expressed
   * by the star since it asserts the existence of an element where the two
   * bags differ. It is moved out of the star, into arithmetic over the
   * cardinalities of the difference bags, using the equivalence
   *   (= A B) iff (and (= (bag.card (bag.difference_subtract A B)) 0)
   *                    (= (bag.card (bag.difference_subtract B A)) 0))
   * The lemma also includes the redundant conjunct
   * (= (bag.card A) (bag.card B)), which gives the arithmetic solver a cheap
   * way to satisfy the negation without unfolding the difference bags.
   *
   * @param equality an equality between two bag terms
   */
  void evictNegatedAtom(const Node& equality);
  /**
   * Step 3 of BagsToLiastar: give every bag term collected so far a slot in
   * the outer vector of the star, i.e. an integer variable that denotes its
   * cardinality. See getCardinalityVar.
   */
  void addCardinalityVars();
  /**
   * Step 4 of BagsToLiastar: build the single star atom
   *   (int.star-contains (lambda ((c_1 Int) ... (c_n Int)) F) x_1 ... x_n)
   * where M_1, ..., M_n are the registered bag terms, x_i is the cardinality
   * variable of M_i, c_i is its bound variable, and F is the conjunction of
   * the sign constraints (>= c_i 0), the pointwise definitions of the M_i
   * (see getPointwiseConstraint) and the pointwise translation (= c_j c_k) of
   * each positive atom (= M_j M_k).
   *
   * Note all the bag atoms are translated into one single star: the body of a
   * star describes one element of the universe, so splitting the atoms into
   * several stars would let each star choose its own universe and lose the
   * correlation between the bags.
   *
   * The star atom holds only in the contexts where the positive atoms it
   * translates hold, so the caller asserts it guarded by them.
   *
   * @param equalities the positive top level bag atoms
   * @param premises the literals of the current context that the body relies
   * on, appended to. The caller asserts the star guarded by them.
   * @return the star atom
   */
  Node buildStar(const std::vector<Node>& equalities,
                 std::vector<Node>& premises);
  /**
   * @param bag a bag term
   * @return the integer variable that denotes the cardinality of bag, i.e. its
   * slot in the outer vector of the star, creating it if needed. The
   * cardinality skolem of the term (bag.card bag) is reused when the input
   * constrains it, so that the star atom relates the cardinality terms of the
   * input. Otherwise a fresh BAGS_LIASTAR_BAG_INTEGER skolem is used, which
   * the star atom is the only constraint on. Either way the variable denotes
   * the cardinality of bag in every context, so no guard is needed for it.
   */
  Node getCardinalityVar(const Node& bag);
  /**
   * The body of the star describes one element e of the universe, and binds
   * one integer variable per bag term: the variable of bag stands for
   * (bag.count e bag), the number of occurrences of e in bag. The star then
   * evaluates the body once per element and adds up the resulting vectors, so
   * the sum of the variable of bag over the summands is the cardinality of
   * bag, which is why it is the slot of bag in the inner vector of the star.
   *
   * @param bag a bag term
   * @return the bound variable of bag, creating it if needed. Since the
   * pointwise definition of a bag operator relates the bound variable of the
   * term to those of its arguments, the arguments of a bag term that has a
   * pointwise translation are registered as well.
   */
  Node getBagBoundVar(const Node& bag);
  /**
   * Figure 4 of [LBPS20] has no rule for a constructed bag (bag e n): its
   * count at an element is not a function of the counts of its arguments, it
   * is n at e and 0 everywhere else, and e is an element and not a bag, so it
   * has no slot in the star. The constraints below pin (bag e n) down without
   * naming e. Writing S for the singleton (bag e 1) and D for
   * (bag.difference_remove (bag e n) S), both of which are slots of the star:
   * - the cardinality of (bag e m) is m when m is positive and 0 otherwise,
   *   which addBagMakeCardinalities asserts outside the star. Applied to S it
   *   gives (= x_S 1), so, the counts being non negative, exactly one summand
   *   of the star has (= c_S 1) and every other summand has (= c_S 0);
   * - D is the empty bag, whatever e and n are, so (= c_D 0) holds at every
   *   element. Together with the pointwise definition of D this says that
   *   (bag e n) has no element outside the one of S, i.e. that its count is
   *   concentrated on the one summand where (= c_S 1);
   * - S is a subbag of (bag e n) when n is positive, hence (<= c_S c_bag).
   *   This conjunct is implied by the two items above, which force the count
   *   of (bag e n) at that summand to be its cardinality n. It is kept as a
   *   redundant constraint, but only when n is a positive constant, since for
   *   a symbolic n it holds only under the side condition (>= n 1), and the
   *   body of the star has no room for a side condition on a term that is not
   *   one of its slots.
   *
   * @param bag a term of kind BAG_MAKE
   * @param constraints the conjuncts of the body of the star, appended to
   */
  void addBagMakeConstraints(const Node& bag, std::vector<Node>& constraints);
  /**
   * State, for every two constructed bags (bag x m) and (bag y n) of the
   * star, whether they sit on the same element. Writing S_x and S_y for their
   * singletons, whose counts are 0 or 1 and sum to 1 over the summands:
   * - when the current context has x and y disequal, S_x and S_y have no
   *   element in common, so (<= (+ c_S_x c_S_y) 1) holds at every element and
   *   the summand carrying S_x is not the one carrying S_y;
   * - when the context has them equal, S_x and S_y are the same bag, so
   *   (= c_S_x c_S_y) holds at every element, which puts the two constructed
   *   bags on the same summand.
   * This is what the body cannot say by itself, since it never names an
   * element. Both conjuncts hold only in the contexts they were read from, so
   * the element literal is added to the premises of the star.
   *
   * A pair whose elements the context has neither equal nor disequal
   * contributes nothing, which only weakens the star. Splitting on the
   * equality of every such pair would decide them all, at the price of a
   * quadratic number of splits; the conjuncts here are deliberately linear
   * and free of ite, since the cone computation of the liastar extension is
   * sensitive to both the dimension and the case split count of the body.
   *
   * @param constraints the conjuncts of the body of the star, appended to
   * @param premises the premises of the star, appended to
   */
  void addBagMakeOverlaps(std::vector<Node>& constraints,
                          std::vector<Node>& premises);
  /**
   * Assert the cardinality of every constructed bag of the star:
   * (= x_(bag e n) (ite (>= n 1) n 0)). This is a fact about the term, so it
   * is asserted as a lemma of its own, outside the star and with no guard.
   * See addBagMakeConstraints.
   */
  void addBagMakeCardinalities();
  /**
   * @param bag a term of kind BAG_MAKE
   * @return the singleton bag (bag e 1) of bag = (bag e n), which is bag
   * itself when n is the constant 1
   */
  Node getBagMakeSingleton(const Node& bag);
  /**
   * @param bag a term of kind BAG_MAKE
   * @return (bag.difference_remove bag (getBagMakeSingleton bag))
   */
  Node getBagMakeDifference(const Node& bag);
  /**
   * @param bag a bag term whose kind has a pointwise translation
   * @return the definition of the bound variable of bag in terms of the bound
   * variables of its arguments, e.g. for (bag.inter_min A B) this is
   * (= c_(A inter B) (ite (<= c_A c_B) c_A c_B))
   * where c_M denotes the bound variable of bag M.
   */
  Node getPointwiseConstraint(const Node& bag);
  /**
   * cvc5 rewrites (bag.subbag A B) into
   * (= (bag.difference_subtract A B) (as bag.empty (Bag T))), so the inclusion
   * rule of the table of BagsToLiastar, which is the linear conjunct
   * (<= c_A c_B), arrives in that form. Recognizing it avoids a slot for the
   * difference and the ite of its pointwise definition, which matters: the
   * cone computation of the liastar extension is exponential in the number of
   * case splits of the body, and a query with five inclusions pays 2^5 times
   * more for nothing.
   *
   * @param equality an equality between two bag terms
   * @param a set to A when the result is true
   * @param b set to B when the result is true
   * @return whether equality is an inclusion atom
   */
  static bool isInclusionAtom(const Node& equality, Node& a, Node& b);
  /**
   * @param k a kind
   * @return whether the count of a term of kind k at an element is a function
   * of the counts of its arguments at that element, which is the case for the
   * bag operators of the lookup table of BagsToLiastar. A constructed bag
   * (bag x c) is not one of them, and is handled by addBagMakeConstraints
   * instead. Terms of any other kind (bag variables, but also e.g.
   * (bag.map f A) or (table.group A)) are slots of the star that carry no
   * definition, which only weakens the star.
   */
  static bool hasPointwiseTranslation(Kind k);
  /** apply inference rules for empty bags */
  void checkEmpty(const Node& n);

  /**
   * apply inference rules for BAG_MAKE operator.
   * Example: Suppose n = (bag x c), and we have two count terms (bag.count x n)
   * and (bag.count y n).
   * This function will add inferences for the count terms as documented in
   * InferenceGenerator::bagMake.
   * Note that element y may not be in bag n. See the documentation of
   * SolverState::getElements.
   */
  void checkBagMake(const Node& n);
  /**
   * @param n is a bag that has the form (op A B)
   * @return the set union of known elements in (op A B) , A, and B.
   */
  std::set<Node> getElementsForBinaryOperator(const Node& n);
  /** apply inference rules for union disjoint */
  void checkUnionDisjoint(const Node& n);
  /** apply inference rules for union max */
  void checkUnionMax(const Node& n);
  /** apply inference rules for intersection_min operator */
  void checkIntersectionMin(const Node& n);
  /** apply inference rules for difference subtract */
  void checkDifferenceSubtract(const Node& n);
  /** apply inference rules for difference remove */
  void checkDifferenceRemove(const Node& n);
  /** apply inference rules for duplicate removal operator */
  void checkSetof(Node n);
  /** apply non negative constraints for multiplicities */
  void checkNonNegativeCountTerms(const Node& bag, const Node& element);
  /** apply inference rules for disequal bag terms */
  void checkDisequalBagTerms();
  /** apply inference rules for map operator */
  void checkMap(Node n);
  /** apply inference rules for filter operator */
  void checkFilter(Node n);
  /** apply inference rules for product operator */
  void checkProduct(Node n);
  /** apply inference rules for join operator */
  void checkJoin(Node n);
  /** apply inference rules for group operator */
  void checkGroup(Node n);

  /** The solver state object */
  SolverState& d_state;
  /** The inference generator object*/
  InferenceGenerator d_ig;
  /** Reference to the inference manager for the theory of bags */
  InferenceManager& d_im;

  /**
   * a map where the keys are nodes of the form (bag.map f A)
   * where f is a function (-> E T), A a bag of type (Bag E),
   * and values are maps where keys are elements y's of (bag.map f A)
   * and values are pairs <uf, preImageSize> such that
   * uf is an uninterpreted function Int -> E represents the and
   * preImageSize is the cardinality of the distinct elements in A that are
   * mapped to each y
   *
   */
  using BagElementsMap = context::CDHashMap<
      Node,
      std::shared_ptr<context::CDHashMap<Node, std::pair<Node, Node> > > >;
  BagElementsMap d_mapCache;

  /**
   * A map from bag terms to the integer variables that denote their
   * cardinalities, i.e. the map card of BagsToLiastar. These variables are the
   * elements of the outer vector of the star atom. This map is cleared and
   * recomputed at the start of each call to checkLiastarConstraints.
   */
  std::map<Node, Node> d_cardinalityVars;
  /**
   * A map from bag terms to their bound variables in the body of the star
   * atom. See getBagBoundVar. These variables are the elements of the inner
   * vector of the star atom, and the keys of this map fix the order of both
   * vectors. This map is cleared and recomputed at the start of each call to
   * checkLiastarConstraints.
   */
  std::map<Node, Node> d_bagBoundVars;

  /** Commonly used constants */
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
}; /* class BagSolver */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAG__SOLVER_H */
