/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of separation logic.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SEP__THEORY_SEP_H
#define CVC5__THEORY__SEP__THEORY_SEP_H

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/cdqueue.h"
#include "theory/decision_strategy.h"
#include "theory/inference_manager_buffered.h"
#include "theory/sep/theory_sep_rewriter.h"
#include "theory/theory.h"
#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {

class TheoryModel;

namespace sep {

class TheorySep : public Theory {
  typedef context::CDList<Node> NodeList;
  typedef context::CDHashSet<Node> NodeSet;
  typedef context::CDHashMap<Node, Node> NodeNodeMap;

  /////////////////////////////////////////////////////////////////////////////
  // MISC
  /////////////////////////////////////////////////////////////////////////////

 private:
  /** True node for predicates = true */
  Node d_true;

  /** True node for predicates = false */
  Node d_false;

  //whether bounds have been initialized
  bool d_bounds_init;

  TheorySepRewriter d_rewriter;
  /** A (default) theory state object */
  TheoryState d_state;
  /** A buffered inference manager */
  InferenceManagerBuffered d_im;

  size_t processAssertion(
      Node n,
      std::map<int, std::map<Node, size_t> >& visited,
      std::map<int, std::map<Node, std::vector<Node> > >& references,
      std::map<int, std::map<Node, bool> >& references_strict,
      bool pol,
      bool hasPol,
      bool underSpatial);

 public:
  TheorySep(Env& env, OutputChannel& out, Valuation valuation);
  ~TheorySep();

  //--------------------------------- initialization
  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /** get the proof checker of this theory */
  ProofRuleChecker* getProofChecker() override;
  /**
   * Returns true if we need an equality engine. If so, we initialize the
   * information regarding how it should be setup. For details, see the
   * documentation in Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi) override;
  /** finish initialization */
  void finishInit() override;
  //--------------------------------- end initialization
  /** preregister term */
  void preRegisterTerm(TNode n) override;

  std::string identify() const override { return std::string("TheorySep"); }

  void ppNotifyAssertions(const std::vector<Node>& assertions) override;

  TrustNode explain(TNode n) override;

  void computeCareGraph() override;

  void postProcessModel(TheoryModel* m) override;

 private:
  /**
   * Initialize heap. For smt2 inputs, this will initialize the heap types
   * based on if a command (declare-heap (locT datat)) was used. This command
   * can be executed once only, and must be invoked before solving separation
   * logic inputs, which is controlled by the solver engine.
   */
  void initializeHeapTypes();
  /** Should be called to propagate the literal.  */
  bool propagateLit(TNode literal);
  /** Conflict when merging constants */
  void conflict(TNode a, TNode b);

 public:

  void presolve() override;

  /////////////////////////////////////////////////////////////////////////////
  // MAIN SOLVER
  /////////////////////////////////////////////////////////////////////////////

  //--------------------------------- standard check
  /** Do we need a check call at last call effort? */
  bool needsCheckLastEffort() override;
  /** Post-check, called after the fact queue of the theory is processed. */
  void postCheck(Effort level) override;
  /** Pre-notify fact, return true if processed. */
  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;
  /** Notify fact */
  void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) override;
  //--------------------------------- end standard check

 private:
  /** Ensures that the reduction has been added for the given fact */
  void reduceFact(TNode atom, bool polarity, TNode fact);
  /** Is spatial kind? */
  bool isSpatialKind(Kind k) const;
  // NotifyClass: template helper class for d_equalityEngine - handles
  // call-back from congruence closure module
  class NotifyClass : public eq::EqualityEngineNotify
  {
    TheorySep& d_sep;

   public:
    NotifyClass(TheorySep& sep) : d_sep(sep) {}

    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override
    {
      Trace("sep::propagate")
          << "NotifyClass::eqNotifyTriggerPredicate(" << predicate << ", "
          << (value ? "true" : "false") << ")" << std::endl;
      Assert(predicate.getKind() == kind::EQUAL);
      // Just forward to sep
      if (value)
      {
        return d_sep.propagateLit(predicate);
      }
      return d_sep.propagateLit(predicate.notNode());
    }
    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override
    {
      Trace("sep::propagate")
          << "NotifyClass::eqNotifyTriggerTermEquality(" << t1 << ", " << t2
          << ", " << (value ? "true" : "false") << ")" << std::endl;
      if (value)
      {
        // Propagate equality between shared terms
        return d_sep.propagateLit(t1.eqNode(t2));
      }
      return d_sep.propagateLit(t1.eqNode(t2).notNode());
    }

    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override
    {
      Trace("sep::propagate") << "NotifyClass::eqNotifyConstantTermMerge(" << t1
                              << ", " << t2 << ")" << std::endl;
      d_sep.conflict(t1, t2);
    }

    void eqNotifyNewClass(TNode t) override {}
    void eqNotifyMerge(TNode t1, TNode t2) override
    {
      d_sep.eqNotifyMerge(t1, t2);
    }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override {}
  };

  /** The notify class for d_equalityEngine */
  NotifyClass d_notify;

  /** list of all refinement lemms */
  std::map< Node, std::map< Node, std::vector< Node > > > d_refinement_lem;

  //cache for positive polarity start reduction
  NodeSet d_reduce;
  std::map< Node, std::map< Node, Node > > d_red_conc;
  std::map< Node, std::map< Node, Node > > d_neg_guard;
  std::vector< Node > d_neg_guards;
  /** a (singleton) decision strategy for each negative guard. */
  std::map<Node, std::unique_ptr<DecisionStrategySingleton> >
      d_neg_guard_strategy;
  std::map< Node, Node > d_guard_to_assertion;
  NodeList d_spatial_assertions;

  //data,ref type (globally fixed)
  TypeNode d_type_ref;
  TypeNode d_type_data;
  //information about types
  Node d_base_label;
  Node d_nil_ref;
  //reference bound
  Node d_reference_bound;
  Node d_reference_bound_max;
  std::vector<Node> d_type_references;
  //kind of bound for reference types
  enum {
    bound_strict,
    bound_default,
    bound_invalid,
  };
  unsigned d_bound_kind;

  std::vector<Node> d_type_references_card;
  std::map< Node, unsigned > d_type_ref_card_id;
  std::vector<Node> d_type_references_all;
  size_t d_card_max;
  //for empty argument
  Node d_emp_arg;
  //map from ( atom, label, child index ) -> label
  std::map< Node, std::map< Node, std::map< int, Node > > > d_label_map;

  /**
   * Maps label sets to their direct parents. A set may have multiple parents
   * if sep.wand constraints are present.
   */
  std::map<Node, std::vector<Node> > d_parentMap;
  /**
   * Maps label sets to their direct children. This map is only stored for
   * labels with children that do not share a root label with the base label.
   */
  std::map<Node, std::vector<Node> > d_childrenMap;

  /**
   * This sends the lemmas:
   *   parent = (set.union children)
   *   (set.inter children_i children_j) = empty, for each i != j
   * It also stores these relationships in d_parentMap.
   */
  void makeDisjointHeap(Node parent, const std::vector<Node>& children);
  /**
   * Get the sets that are parents of p and are roots in the graph induced
   * by d_parentMap.
   */
  std::vector<Node> getRootLabels(Node p) const;
  /**
   * Do p and q have a root label in common?
   */
  bool sharesRootLabel(Node p, Node q) const;

  //term model
  std::map< Node, Node > d_tmodel;
  std::map< Node, Node > d_pto_model;

  /**
   * A heap assert info is maintained per set equivalence class. It is
   * used to ensure that list of positive and negative pto constraints for
   * all label sets that are equal to a given one are satisfied.
   *
   * Note that sets referring to subsets of different heaps may become equated,
   * e.g. if wand constraints are present. Thus, we keep a list of pto
   * constraints, which track their labels. In the checkPto method, we
   * distinguish whether the pto constraints refer to the same heap.
   */
  class HeapAssertInfo {
  public:
   HeapAssertInfo(context::Context* c);
   ~HeapAssertInfo() {}
   /** List of positive pto */
   NodeList d_posPto;
   /** List of negative pto */
   NodeList d_negPto;
  };
  std::map< Node, HeapAssertInfo * > d_eqc_info;
  HeapAssertInfo * getOrMakeEqcInfo( Node n, bool doMake = false );

  /**
   * Ensure that reference and data types have been set to something that is
   * non-null, and compatible with separation logic constraint atom.
   */
  void ensureHeapTypesFor(Node atom) const;
  /**
   * This is called either when:
   * (A) a declare-heap command is issued with tn1/tn2, and atom is null, or
   * (B) an atom specifying the heap type tn1/tn2 is registered to this theory.
   * We set the heap type if we are are case (A), and check whether the
   * heap type is consistent in the case of (B).
   */
  void registerRefDataTypes(TypeNode tn1, TypeNode tn2, Node atom);
  //get location/data type
  //get the base label for the spatial assertion
  Node getBaseLabel();
  Node getLabel( Node atom, int child, Node lbl );
  /**
   * Apply label lbl to all top-level spatial assertions, recursively, in n.
   */
  Node applyLabel( Node n, Node lbl, std::map< Node, Node >& visited );
  void getLabelChildren( Node atom, Node lbl, std::vector< Node >& children, std::vector< Node >& labels );

  class HeapInfo {
  public:
    HeapInfo() : d_computed(false) {}
    //information about the model
    bool d_computed;
    std::vector< Node > d_heap_locs;
    std::vector< Node > d_heap_locs_model;
    //get value
    Node getValue( TypeNode tn );
  };
  //heap info ( label -> HeapInfo )
  std::map< Node, HeapInfo > d_label_model;
  /**
   * This checks the impact of adding the pto assertion p to heap assert info e,
   * where p has been asserted with the given polarity.
   *
   * This method implements two propagation schemes for pairs of
   * positive/positive and positive/negative pto constraints.
   *
   * @param e The heap assert info
   * @param p The (label) pto constraint
   * @param polarity Its asserted polarity
   * @return true if p should be added to the list of constraints in e, false
   * if the constraint was redundant.
   */
  bool checkPto(HeapAssertInfo* e, Node p, bool polarity);
  void computeLabelModel( Node lbl );
  Node instantiateLabel(Node n,
                        Node o_lbl,
                        Node lbl,
                        Node lbl_v,
                        std::map<Node, Node>& visited,
                        std::map<Node, Node>& pto_model,
                        TypeNode rtn,
                        std::map<Node, bool>& active_lbl,
                        unsigned ind = 0);
  void setInactiveAssertionRec( Node fact, std::map< Node, std::vector< Node > >& lbl_to_assertions, std::map< Node, bool >& assert_active );

  Node mkUnion( TypeNode tn, std::vector< Node >& locs );

  Node getRepresentative( Node t );
  bool hasTerm( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  void eqNotifyMerge(TNode t1, TNode t2);

  void sendLemma( std::vector< Node >& ant, Node conc, InferenceId id, bool infer = false );
  void doPending();

  void initializeBounds();
};/* class TheorySep */

}  // namespace sep
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SEP__THEORY_SEP_H */
