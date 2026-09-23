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
   * Translate the bag constraints of the current context into one liastar
   * star-contains atom, following algorithm MapaToLiaStar of the paper
   * "Deciding Boolean Algebra with Presburger Arithmetic", extended to
   * multisets.
   *
   * Steps 1 and 2 of that algorithm are taken care of by cvc5:
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
   * Note the star atom constrains the cardinality variables of the bags, not
   * their values, and nothing reads back the decomposition it witnesses. So
   * the translation is refutation oriented: the bag values of a model do not
   * necessarily satisfy the cardinality constraints of the input.
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
   * Step 1 of MapaToLiaStar for a negated bag atom, which cannot be expressed
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
   * Step 3 of MapaToLiaStar: give every bag term collected so far a slot in
   * the outer vector of the star, i.e. an integer variable that denotes its
   * cardinality. See getCardinalityVar.
   */
  void addCardinalityVars();
  /**
   * Step 4 of MapaToLiaStar: build the single star atom
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
   * @return the star atom
   */
  Node buildStar(const std::vector<Node>& equalities);
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
   * @param bag a bag term whose kind has a pointwise translation
   * @return the definition of the bound variable of bag in terms of the bound
   * variables of its arguments, e.g. for (bag.inter_min A B) this is
   * (= c_(A inter B) (ite (<= c_A c_B) c_A c_B))
   * where c_M denotes the bound variable of bag M.
   */
  Node getPointwiseConstraint(const Node& bag);
  /**
   * @param k a kind
   * @return whether the count of a term of kind k at an element is a function
   * of the counts of its arguments at that element, which is the case for the
   * bag operators of the lookup table of MapaToLiaStar. Terms of any other
   * kind (bag variables, but also e.g. (bag x c), (bag.map f A) or
   * (table.group A)) are slots of the star that carry no definition, which
   * only weakens the star.
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
   * cardinalities, i.e. the map card of MapaToLiaStar. These variables are the
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
