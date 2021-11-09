/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Kshitij Bansal, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "theory/sets/cardinality_extension.h"
#include "theory/sets/inference_manager.h"
#include "theory/sets/solver_state.h"
#include "theory/sets/term_registry.h"
#include "theory/sets/theory_sets_rels.h"
#include "theory/sets/theory_sets_rewriter.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace cvc5 {
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
  /** Are a and b trigger terms in the equality engine that may be disequal? */
  bool areCareDisequal(Node a, Node b);
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
   * This implements a strategy for splitting for set disequalities which
   * roughly corresponds the SET DISEQUALITY rule from Bansal et al IJCAR 2016.
   */
  void checkDisequalities();
  /**
   * Check comprehensions. This adds reduction lemmas for all set comprehensions
   * in the current context.
   */
  void checkReduceComprehensions();

  void addCarePairs(TNodeTrie* t1,
                    TNodeTrie* t2,
                    unsigned arity,
                    unsigned depth,
                    unsigned& n_pairs);

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
    EqcInfo( context::Context* c );
    ~EqcInfo(){}
    // singleton or emptyset equal to this eqc
    context::CDO< Node > d_singleton;
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
  std::map< Node, TypeNode > d_most_common_type;
  std::map< Node, Node > d_most_common_type_term;

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
                    ProofNodeManager* pnm);

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
  void addSharedTerm(TNode);
  bool collectModelValues(TheoryModel* m, const std::set<Node>& termSet);

  void computeCareGraph();

  Node explain(TNode);

  void preRegisterTerm(TNode node);

  /** ppRewrite, which expands choose and is_singleton.  */
  TrustNode ppRewrite(Node n, std::vector<SkolemLemma>& lems);

  void presolve();

  /** get the valuation */
  Valuation& getValuation();
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

 public:
  /** Is formula n entailed to have polarity pol in the current context? */
  bool isEntailed(Node n, bool pol) { return d_state.isEntailed(n, pol); }

 private:

  /** expand the definition of the choose operator */
  TrustNode expandChooseOperator(const Node& node,
                                 std::vector<SkolemLemma>& lems);
  /** expand the definition of is_singleton operator */
  TrustNode expandIsSingletonOperator(const Node& node);
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

  /** The theory rewriter for this theory. */
  TheorySetsRewriter d_rewriter;

  /** a map that maps each set to an existential quantifier generated for
   * operator is_singleton */
  std::map<Node, Node> d_isSingletonNodes;
}; /* class TheorySetsPrivate */

}  // namespace sets
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__SETS__THEORY_SETS_PRIVATE_H */
