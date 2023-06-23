/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Kshitij Bansal
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sets theory implementation.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SETS__THEORY_SETS_PRIVATE_H
#define CVC5__THEORY__SETS__THEORY_SETS_PRIVATE_H

#include "context/cdhashset.h"
#include "context/cdqueue.h"
#include "expr/node_trie.h"
#include "smt/env_obj.h"
#include "theory/care_pair_argument_callback.h"
#include "theory/sets/cardinality_extension.h"
#include "theory/sets/inference_manager.h"
#include "theory/sets/solver_state.h"
#include "theory/sets/term_registry.h"
#include "theory/sets/theory_sets_rels.h"
#include "theory/sets/theory_sets_rewriter.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

/** Internal classes, forward declared here */
class TheorySets;

class TheorySetsPrivate : protected EnvObj
{
  typedef context::CDHashMap<Node, bool> NodeBoolMap;
  typedef context::CDHashSet<Node> NodeSet;

 public:
  void eqNotifyNewClass(TNode t);
  void eqNotifyMerge(TNode t1, TNode t2);
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);

 private:
  /**
   * Invoke the decision procedure for this theory, which is run at
   * full effort. This will either send a lemma or conflict on the output
   * channel of this class, or otherwise the current set of constraints is
   * satisfiable w.r.t. the theory of sets.
   */
  void fullEffortCheck();
  /**
   * Reset the information for a full effort check.
   */
  void fullEffortReset();
  /**
   * This implements an inference schema based on the "downwards closure" of
   * set membership. This roughly corresponds to the rules SET_UNION DOWN I and
   * II, INTER DOWN I and II from Bansal et al IJCAR 2016, as well as rules for
   * set difference.
   */
  void checkDownwardsClosure();
  /**
   * This implements an inference schema based on the "upwards closure" of
   * set membership. This roughly corresponds to the rules SET_UNION UP, INTER
   * UP I and II from Bansal et al IJCAR 2016, as well as rules for set
   * difference.
   */
  void checkUpwardsClosure();

  /**
   * Apply the following rule for filter terms (set.filter p A):
   * (=>
   *   (and (set.member x B) (= A B))
   *   (or
   *    (and (p x) (set.member x (set.filter p A)))
   *    (and (not (p x)) (not (set.member x (set.filter p A))))
   *   )
   * )
   */
  void checkFilterUp();
  /**
   * Apply the following rule for filter terms (set.filter p A):
   * (=>
   *   (bag.member x (set.filter p A))
   *   (and
   *    (p x)
   *    (set.member x A)
   *   )
   * )
   */
  void checkFilterDown();

  /**
   * Apply the following rule for map terms (set.map f A):
   * Positive member rule:
   * (=>
   *   (set.member x A)
   *   (set.member (f x) (set.map f A)
   * )
   */
  void checkMapUp();
  /**
   * Apply the following rules for map terms (set.map f A) where A has type
   * (Set T):
   * - General case:
   *   (=>
   *     (set.member y (set.map f A))
   *     (and
   *       (= (f x) y)
   *       (set.member x A)
   *     )
   *   )
   *   where x is a fresh skolem
   * - Special case where we can avoid skolems
   *   (=>
   *     (set.member (f x) (set.map f A))
   *     (set.member x A)
   *   )
   */
  void checkMapDown();
  void checkGroups();
  void checkGroup(Node n);
  /**
   * @param n has form ((_ rel.group n1 ... nk) A) where A has type T
   * @return an inference that represents:
   * (=>
   *  (= A (as set.empty T))
   *  (= skolem (set.singleton (as set.empty T)))
   * )
   */
  void groupNotEmpty(Node n);
  /**
   * @param n has form ((_ rel.group n1 ... nk) A) where A has type (Relation T)
   * @param e an element of type T
   * @param part a skolem function of type T -> (Relation T) created uniquely
   * for n by defineSkolemPartFunction function below
   * @return an inference that represents:
   * (=>
   *   (set.member x A)
   *   (and
   *     (set.member (part x) skolem)
   *     (set.member x (part x))
   *     (not (set.member (as set.empty (Relation T)) skolem))
   *   )
   * )
   *
   * where skolem is a variable equals ((_ rel.group n1 ... nk) A)
   */
  void groupUp1(Node n, Node x, Node part);
  /**
   * @param n has form ((_ rel.group n1 ... nk) A) where A has type (Relation T)
   * @param e an element of type T
   * @param part a skolem function of type T -> (Relation T) created uniquely
   * for n by defineSkolemPartFunction function below
   * @return an inference that represents:
   * (=>
   *   (not (set.member x A))
   *   (= (part x) (as set.empty (Relation T)))
   * )
   *
   * where skolem is a variable equals ((_ rel.group n1 ... nk) A)
   */
  void groupUp2(Node n, Node x, Node part);
  /**
   * @param n has form ((_ rel.group n1 ... nk) A) where A has type (Relation T)
   * @param B an element of type (Relation T)
   * @param x an element of type T
   * @param part a skolem function of type T -> (Relation T) created uniquely
   * for n by defineSkolemPartFunction function below
   * @return an inference that represents:
   * (=>
   *   (and
   *     (set.member B skolem)
   *     (set.member x B)
   *   )
   *   (and
   *     (set.member x A)
   *     (= (part x) B)
   *   )
   * )
   * where skolem is a variable equals ((_ table.group n1 ... nk) A).
   */
  void groupDown(Node n, Node B, Node x, Node part);
  /**
   * @param n has form ((_ rel.group n1 ... nk) A) where A has type (Relation T)
   * @param B an element of type (Relation T) and B is not of the form (part x)
   * @param part a skolem function of type T -> (Relation T) created uniquely
   * for n by defineSkolemPartFunction function below
   * @return an inference that represents:
   * (=>
   *   (and
   *     (set.member B skolem)
   *     (not (= A (as set.empty (Relation T)))
   *   )
   *   (and
   *     (= B (part k_{n, B}))
   *     (set.member k_{n,B} B)
   *     (set.member k_{n,B} A)
   *   )
   * )
   * where skolem is a variable equals ((_ rel.group n1 ... nk) A), and
   * k_{n, B} is a fresh skolem of type T.
   */
  void groupPartMember(Node n, Node B, Node part);
  /**
   * @param n has form ((_ rel.group n1 ... nk) A) where A has type (Relation T)
   * @param B an element of type (Relation T)
   * @param x an element of type T
   * @param y an element of type T
   * @param part a skolem function of type T -> (Relation T) created uniquely
   * for n by defineSkolemPartFunction function below
   * @return an inference that represents:
   * (=>
   *   (and
   *     (set.member B skolem)
   *     (set.member x B)
   *     (set.member y B)
   *     (distinct x y)
   *   )
   *   (and
   *     (= ((_ tuple.project n1 ... nk) x)
   *        ((_ tuple.project n1 ... nk) y))
   *     (= (part x) (part y))
   *     (= (part x) B)
   *   )
   * )
   * where skolem is a variable equals ((_ rel.group n1 ... nk) A).
   */
  void groupSameProjection(Node n, Node B, Node x, Node y, Node part);
  /**
   * @param n has form ((_ rel.group n1 ... nk) A) where A has type (Relation T)
   * @param B an element of type (Relation T)
   * @param x an element of type T
   * @param y an element of type T
   * @param part a skolem function of type T -> (Relation T) created uniquely
   * for n by defineSkolemPartFunction function below
   * @return an inference that represents:
   * (=>
   *   (and
   *     (set.member B skolem)
   *     (set.member x B)
   *     (set.member y A)
   *     (distinct x y)
   *     (= ((_ tuple.project n1 ... nk) x)
   *        ((_ tuple.project n1 ... nk) y))
   *   )
   *   (and
   *     (set.member y B)
   *     (= (part x) (part y))
   *     (= (part x) B)
   *   )
   * )
   * where skolem is a variable equals ((_ rel.group n1 ... nk) A).
   */
  void groupSamePart(Node n, Node B, Node x, Node y, Node part);
  /**
   * @param n has form ((_ rel.group n1 ... nk) A) where A has type (Relation T)
   * @return a function of type T -> (Relation T) that maps elements T to a
   * part in the partition
   */
  Node defineSkolemPartFunction(Node n);
  /**
   * generate skolem variable for node n and add pending lemma for the equality
   */
  Node registerAndAssertSkolemLemma(Node& n);
  /**
   * This implements a strategy for splitting for set disequalities which
   * roughly corresponds the SET DISEQUALITY rule from Bansal et al IJCAR 2016.
   */
  void checkDisequalities();
  /**
   * Check comprehensions. This adds reduction lemmas for all set comprehensions
   * in the current context.
   */
  void checkReduceComprehensions();

  Node d_true;
  Node d_false;
  Node d_zero;
  NodeBoolMap d_deq;
  /**
   * The set of terms that we have reduced via a lemma in the current user
   * context.
   */
  NodeSet d_termProcessed;
  
  //propagation
  class EqcInfo
  {
  public:
   EqcInfo(context::Context* c);
   ~EqcInfo() {}
   // singleton or emptyset equal to this eqc
   context::CDO<Node> d_singleton;
  };
  /** information necessary for equivalence classes */
  std::map< Node, EqcInfo* > d_eqc_info;
  /** get or make eqc info */
  EqcInfo* getOrMakeEqcInfo( TNode n, bool doMake = false );

  /** full check incomplete
   *
   * This flag is set to true during a full effort check if this theory
   * is incomplete for some reason (for instance, if we combine cardinality
   * with a relation or extended function kind).
   */
  bool d_fullCheckIncomplete;
  /** The reason we set the above flag to true */
  IncompleteId d_fullCheckIncompleteId;

 public:

  /**
   * Constructs a new instance of TheorySetsPrivate w.r.t. the provided
   * contexts.
   */
  TheorySetsPrivate(Env& env,
                    TheorySets& external,
                    SolverState& state,
                    InferenceManager& im,
                    SkolemCache& skc,
                    CarePairArgumentCallback& cpacb);

  ~TheorySetsPrivate();

  TheoryRewriter* getTheoryRewriter() { return &d_rewriter; }

  /** Get the solver state */
  SolverState* getSolverState() { return &d_state; }

  /**
   * Finish initialize, called after the equality engine of theory sets has
   * been determined.
   */
  void finishInit();

  //--------------------------------- standard check
  /** Post-check, called after the fact queue of the theory is processed. */
  void postCheck(Theory::Effort level);
  /** Notify new fact */
  void notifyFact(TNode atom, bool polarity, TNode fact);
  //--------------------------------- end standard check

  /** Collect model values in m based on the relevant terms given by termSet */
  bool collectModelValues(TheoryModel* m, const std::set<Node>& termSet);

  void computeCareGraph();

  Node explain(TNode);

  void preRegisterTerm(TNode node);

  /** ppRewrite, which expands choose and is_singleton.  */
  TrustNode ppRewrite(Node n, std::vector<SkolemLemma>& lems);

  void presolve();

  /** get the valuation */
  Valuation& getValuation();
  /** Is formula n entailed to have polarity pol in the current context? */
  bool isEntailed(Node n, bool pol);

  /**
   * Adds inferences for splitting on arguments of a and b that are not
   * equal nor disequal and are sets.
   */
  void processCarePairArgs(TNode a, TNode b);

  /** returns whether the given kind is a higher order kind for sets. */
  bool isHigherOrderKind(Kind k);

 private:
  TheorySets& d_external;
  /** The state of the sets solver at full effort */
  SolverState& d_state;
  /** The inference manager of the sets solver */
  InferenceManager& d_im;
  /** Reference to the skolem cache */
  SkolemCache& d_skCache;
  /** The term registry */
  TermRegistry d_treg;

  /** Pointer to the equality engine of theory of sets */
  eq::EqualityEngine* d_equalityEngine;

  bool isCareArg( Node n, unsigned a );

  /** expand the definition of the choose operator */
  TrustNode expandChooseOperator(const Node& node,
                                 std::vector<SkolemLemma>& lems);
  /** expand the definition of is_singleton operator */
  TrustNode expandIsSingletonOperator(const Node& node);
  /** ensure that the set type is over first class type, throw logic exception
   * if not */
  void ensureFirstClassSetType(TypeNode tn) const;
  /** subtheory solver for the theory of relations */
  std::unique_ptr<TheorySetsRels> d_rels;
  /** subtheory solver for the theory of sets with cardinality */
  std::unique_ptr<CardinalityExtension> d_cardSolver;
  /** are relations enabled?
   *
   * This flag is set to true during a full effort check if any constraint
   * involving relational constraints is asserted to this theory.
   */
  bool d_rels_enabled;
  /** is cardinality enabled?
   *
   * This flag is set to true during a full effort check if any constraint
   * involving cardinality constraints is asserted to this theory.
   */
  bool d_card_enabled;

  /** are higher order set operators enabled?
   *
   * This flag is set to true during a full effort check if any
   * higher order constraints is asserted to this theory.
   */
  bool d_higher_order_kinds_enabled;

  /** The theory rewriter for this theory. */
  TheorySetsRewriter d_rewriter;

  /** a map that maps each set to an existential quantifier generated for
   * operator is_singleton */
  std::map<Node, Node> d_isSingletonNodes;
  /** Reference to care pair argument callback, used for theory combination */
  CarePairArgumentCallback& d_cpacb;
}; /* class TheorySetsPrivate */

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SETS__THEORY_SETS_PRIVATE_H */
