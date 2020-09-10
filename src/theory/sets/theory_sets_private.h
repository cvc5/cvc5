/*********************                                                        */
/*! \file theory_sets_private.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Sets theory implementation.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H
#define CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H

#include "context/cdhashset.h"
#include "context/cdqueue.h"
#include "expr/node_trie.h"
#include "theory/sets/cardinality_extension.h"
#include "theory/sets/inference_manager.h"
#include "theory/sets/solver_state.h"
#include "theory/sets/theory_sets_rels.h"
#include "theory/sets/theory_sets_rewriter.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace sets {

/** Internal classes, forward declared here */
class TheorySets;

class TheorySetsPrivate {
  typedef context::CDHashMap< Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashMap< Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  void eqNotifyNewClass(TNode t);
  void eqNotifyPreMerge(TNode t1, TNode t2);
  void eqNotifyPostMerge(TNode t1, TNode t2);
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
  /** Assert fact holds in the current context with explanation exp.
   *
   * exp should be explainable by the equality engine of this class, and fact
   * should be a literal.
   */
  bool assertFact(Node fact, Node exp);

 private:
  /** Are a and b trigger terms in the equality engine that may be disequal? */
  bool areCareDisequal(Node a, Node b);
  NodeIntMap d_members;
  std::map< Node, std::vector< Node > > d_members_data;
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
   * This ensures that subtype constraints are met for all set terms. In
   * particular, for a set equivalence class E, let Set(T) be the most
   * common type among the types of terms in that class. In other words,
   * if E contains two terms of Set(Int) and Set(Real), then Set(Int) is the
   * most common type. Then, for each membership x in S where S is a set in
   * this equivalence class, we ensure x has type T by asserting:
   *   x = k
   * for a fresh constant k of type T. This is done only if the type of x is not
   * a subtype of Int (e.g. if x is of type Real). We call k the "type
   * constraint skolem for x of type Int".
   */
  void checkSubtypes();
  /**
   * This implements an inference schema based on the "downwards closure" of
   * set membership. This roughly corresponds to the rules UNION DOWN I and II,
   * INTER DOWN I and II from Bansal et al IJCAR 2016, as well as rules for set
   * difference.
   */
  void checkDownwardsClosure();
  /**
   * This implements an inference schema based on the "upwards closure" of
   * set membership. This roughly corresponds to the rules UNION UP, INTER
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
  NodeSet d_keep;
  
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
  bool d_full_check_incomplete;
  std::map< Node, TypeNode > d_most_common_type;
  std::map< Node, Node > d_most_common_type_term;

 public:

  /**
   * Constructs a new instance of TheorySetsPrivate w.r.t. the provided
   * contexts.
   */
  TheorySetsPrivate(TheorySets& external,
                    context::Context* c,
                    context::UserContext* u);

  ~TheorySetsPrivate();

  TheoryRewriter* getTheoryRewriter() { return &d_rewriter; }

  void setMasterEqualityEngine(eq::EqualityEngine* eq);

  void addSharedTerm(TNode);

  void check(Theory::Effort);

  bool collectModelInfo(TheoryModel* m);

  void computeCareGraph();

  Node explain(TNode);

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  void preRegisterTerm(TNode node);

  /** expandDefinition
   * If the sets-ext option is not set and we have an extended operator, 
   * we throw an exception. This function is a no-op otherwise.
   *
   * TheorySets uses expandDefinition as an entry point to see if the input
   * contains extended operators.
   *
   * We need to be notified when a universe set occurs in our input,
   * before preprocessing and simplification takes place. Otherwise the models
   * may be inaccurate when setsExt is false, here is an example:
   *
   * x,y : (Set Int)
   * x = (as univset (Set Int));
   * 0 in y;
   * check-sat;
   *
   * If setsExt is enabled, the model value of (as univset (Set Int)) is always accurate.
   *
   * If setsExt is not enabled, the following can happen for the above example:
   * x = (as univset (Set Int)) is made into a model substitution during 
   * simplification. This means (as univset (Set Int)) is not a term in any assertion, 
   * and hence we do not throw an exception, nor do we infer that 0 is a member of 
   * (as univset (Set Int)). We instead report a model where x = {}. The correct behavior 
   * is to throw an exception that says universe set is not supported when setsExt disabled.
   * Hence we check for the existence of universe set before simplification here.
   *
   * Another option to fix this is to make TheoryModel::getValue more general
   * so that it makes theory-specific calls to evaluate interpreted symbols.
   */
  Node expandDefinition(Node n);
  
  void presolve();

  void propagate(Theory::Effort);

  /** get default output channel */
  OutputChannel* getOutputChannel();
  /** get the valuation */
  Valuation& getValuation();

 private:
  TheorySets& d_external;

  /** Functions to handle callbacks from equality engine */
  class NotifyClass : public eq::EqualityEngineNotify {
    TheorySetsPrivate& d_theory;

  public:
    NotifyClass(TheorySetsPrivate& theory): d_theory(theory) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value) override;
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override;
    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override;
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override;
    void eqNotifyNewClass(TNode t) override;
    void eqNotifyPreMerge(TNode t1, TNode t2) override;
    void eqNotifyPostMerge(TNode t1, TNode t2) override;
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override;
  } d_notify;

  /** Equality engine */
  eq::EqualityEngine d_equalityEngine;

  /** Proagate out to output channel */
  bool propagate(TNode);

  /** generate and send out conflict node */
  void conflict(TNode, TNode);
  
  bool isCareArg( Node n, unsigned a );

 public:
  /** Is formula n entailed to have polarity pol in the current context? */
  bool isEntailed(Node n, bool pol) { return d_state.isEntailed(n, pol); }
  /** Is x entailed to be a member of set s in the current context? */
  bool isMember(Node x, Node s);

 private:
  /** get choose function
   *
   * Returns the existing uninterpreted function for the choose operator for the
   * given set type, or creates a new one if it does not exist.
   */
  Node getChooseFunction(const TypeNode& setType);
  /** The state of the sets solver at full effort */
  SolverState d_state;
  /** The inference manager of the sets solver */
  InferenceManager d_im;
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

  /*
   * a map that stores the choose functions for set types
   */
  std::map<TypeNode, Node> d_chooseFunctions;
};/* class TheorySetsPrivate */


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H */
