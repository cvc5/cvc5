/*********************                                                        */
/*! \file theory_sep.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Dejan Jovanovic, Clark Barrett
 ** Minor contributors (to current version): Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of sep
 **
 ** Theory of sep.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SEP__THEORY_SEP_H
#define __CVC4__THEORY__SEP__THEORY_SEP_H

#include "theory/theory.h"
#include "util/statistics_registry.h"
#include "theory/uf/equality_engine.h"
#include "context/cdchunk_list.h"
#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdqueue.h"

namespace CVC4 {
namespace theory {

class TheoryModel;

namespace sep {

class TheorySep : public Theory {
  typedef context::CDChunkList<Node> NodeList;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;

  /////////////////////////////////////////////////////////////////////////////
  // MISC
  /////////////////////////////////////////////////////////////////////////////

  private:
  /** all lemmas sent */
  NodeSet d_lemmas_produced_c;

  /** True node for predicates = true */
  Node d_true;

  /** True node for predicates = false */
  Node d_false;
  
  //whether bounds have been initialized
  bool d_bounds_init;

  Node mkAnd( std::vector< TNode >& assumptions );

  int processAssertion( Node n, std::map< int, std::map< Node, int > >& visited, 
                        std::map< int, std::map< Node, std::vector< Node > > >& references, std::map< int, std::map< Node, bool > >& references_strict,
                        bool pol, bool hasPol, bool underSpatial );

  public:

  TheorySep(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo);
  ~TheorySep();

  void setMasterEqualityEngine(eq::EqualityEngine* eq);

  std::string identify() const { return std::string("TheorySep"); }

  /////////////////////////////////////////////////////////////////////////////
  // PREPROCESSING
  /////////////////////////////////////////////////////////////////////////////

  public:

  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions);
  Node ppRewrite(TNode atom);
  
  void ppNotifyAssertions( std::vector< Node >& assertions );
  /////////////////////////////////////////////////////////////////////////////
  // T-PROPAGATION / REGISTRATION
  /////////////////////////////////////////////////////////////////////////////

  private:

  /** Should be called to propagate the literal.  */
  bool propagate(TNode literal);

  /** Explain why this literal is true by adding assumptions */
  void explain(TNode literal, std::vector<TNode>& assumptions);

  public:

  void propagate(Effort e);
  Node explain(TNode n);

  public:

  void addSharedTerm(TNode t);
  EqualityStatus getEqualityStatus(TNode a, TNode b);
  void computeCareGraph();

  /////////////////////////////////////////////////////////////////////////////
  // MODEL GENERATION
  /////////////////////////////////////////////////////////////////////////////

  public:

  void collectModelInfo(TheoryModel* m, bool fullModel);
  void postProcessModel(TheoryModel* m);

  /////////////////////////////////////////////////////////////////////////////
  // NOTIFICATIONS
  /////////////////////////////////////////////////////////////////////////////

  private:
  public:

  Node getNextDecisionRequest( unsigned& priority );

  void presolve();
  void shutdown() { }

  /////////////////////////////////////////////////////////////////////////////
  // MAIN SOLVER
  /////////////////////////////////////////////////////////////////////////////
  public:

  void check(Effort e);

  bool needsCheckLastEffort();

  private:

  // NotifyClass: template helper class for d_equalityEngine - handles call-back from congruence closure module
  class NotifyClass : public eq::EqualityEngineNotify {
    TheorySep& d_sep;
  public:
    NotifyClass(TheorySep& sep): d_sep(sep) {}

    bool eqNotifyTriggerEquality(TNode equality, bool value) {
      Debug("sep::propagate") << "NotifyClass::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false") << ")" << std::endl;
      // Just forward to sep
      if (value) {
        return d_sep.propagate(equality);
      } else {
        return d_sep.propagate(equality.notNode());
      }
    }

    bool eqNotifyTriggerPredicate(TNode predicate, bool value) {
      Unreachable();
    }

    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
      Debug("sep::propagate") << "NotifyClass::eqNotifyTriggerTermEquality(" << t1 << ", " << t2 << ", " << (value ? "true" : "false") << ")" << std::endl;
      if (value) {
        // Propagate equality between shared terms
        return d_sep.propagate(t1.eqNode(t2));
      } else {
        return d_sep.propagate(t1.eqNode(t2).notNode());
      }
      return true;
    }

    void eqNotifyConstantTermMerge(TNode t1, TNode t2) {
      Debug("sep::propagate") << "NotifyClass::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << ")" << std::endl;
      d_sep.conflict(t1, t2);
    }

    void eqNotifyNewClass(TNode t) { }
    void eqNotifyPreMerge(TNode t1, TNode t2) { d_sep.eqNotifyPreMerge( t1, t2 ); }
    void eqNotifyPostMerge(TNode t1, TNode t2) { d_sep.eqNotifyPostMerge( t1, t2 ); }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) { }
  };

  /** The notify class for d_equalityEngine */
  NotifyClass d_notify;

  /** Equaltity engine */
  eq::EqualityEngine d_equalityEngine;

  /** Are we in conflict? */
  context::CDO<bool> d_conflict;
  std::vector< Node > d_pending_exp;
  std::vector< Node > d_pending;
  std::vector< int > d_pending_lem;

  /** list of all refinement lemms */
  std::map< Node, std::map< Node, std::vector< Node > > > d_refinement_lem;

  /** Conflict when merging constants */
  void conflict(TNode a, TNode b);

  //cache for positive polarity start reduction
  NodeSet d_reduce;
  std::map< Node, std::map< Node, Node > > d_red_conc;
  std::map< Node, std::map< Node, Node > > d_neg_guard;
  std::vector< Node > d_neg_guards;
  std::map< Node, Node > d_guard_to_assertion;
  /** inferences: maintained to ensure ref count for internally introduced nodes */
  NodeList d_infer;
  NodeList d_infer_exp;
  NodeList d_spatial_assertions;

  //data,ref type (globally fixed)
  TypeNode d_type_ref;
  TypeNode d_type_data;
  //currently fix one data type for each location type, throw error if using more than one
  std::map< TypeNode, TypeNode > d_loc_to_data_type;
  //information about types
  std::map< TypeNode, Node > d_base_label;
  std::map< TypeNode, Node > d_nil_ref;
  //reference bound
  std::map< TypeNode, Node > d_reference_bound;
  std::map< TypeNode, Node > d_reference_bound_max;
  std::map< TypeNode, std::vector< Node > > d_type_references;
  //kind of bound for reference types
  enum {
    bound_strict,
    bound_default,
    bound_herbrand,
    bound_invalid,
  };
  std::map< TypeNode, unsigned > d_bound_kind;
  
  std::map< TypeNode, std::vector< Node > > d_type_references_card;
  std::map< Node, unsigned > d_type_ref_card_id;
  std::map< TypeNode, std::vector< Node > > d_type_references_all;
  std::map< TypeNode, unsigned > d_card_max;
  //for empty argument
  std::map< TypeNode, Node > d_emp_arg;
  //map from ( atom, label, child index ) -> label
  std::map< Node, std::map< Node, std::map< int, Node > > > d_label_map;
  std::map< Node, Node > d_label_map_parent;

  //term model
  std::map< Node, Node > d_tmodel;
  std::map< Node, Node > d_pto_model;

  class HeapAssertInfo {
  public:
    HeapAssertInfo( context::Context* c );
    ~HeapAssertInfo(){}
    context::CDO< Node > d_pto;
    context::CDO< bool > d_has_neg_pto;
  };
  std::map< Node, HeapAssertInfo * > d_eqc_info;
  HeapAssertInfo * getOrMakeEqcInfo( Node n, bool doMake = false );

  //get global reference/data type
  TypeNode getReferenceType( Node n );
  TypeNode getDataType( Node n );
  void registerRefDataTypes( TypeNode tn1, TypeNode tn2, Node atom );
  //get location/data type
  //get the base label for the spatial assertion
  Node getBaseLabel( TypeNode tn );
  Node getNilRef( TypeNode tn );
  void setNilRef( TypeNode tn, Node n );
  Node getLabel( Node atom, int child, Node lbl );
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
  // loc -> { data_1, ..., data_n } where (not (pto loc data_1))...(not (pto loc data_n))).
  std::map< Node, std::vector< Node > > d_heap_locs_nptos;

  void debugPrintHeap( HeapInfo& heap, const char * c );
  void validatePto( HeapAssertInfo * ei, Node ei_n );
  void addPto( HeapAssertInfo * ei, Node ei_n, Node p, bool polarity );
  void mergePto( Node p1, Node p2 );
  void computeLabelModel( Node lbl );
  Node instantiateLabel( Node n, Node o_lbl, Node lbl, Node lbl_v, std::map< Node, Node >& visited, std::map< Node, Node >& pto_model, 
                         TypeNode rtn, std::map< Node, bool >& active_lbl, unsigned ind = 0 );
  void setInactiveAssertionRec( Node fact, std::map< Node, std::vector< Node > >& lbl_to_assertions, std::map< Node, bool >& assert_active );

  Node mkUnion( TypeNode tn, std::vector< Node >& locs );
private:
  Node getRepresentative( Node t );
  bool hasTerm( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  void eqNotifyPreMerge(TNode t1, TNode t2);
  void eqNotifyPostMerge(TNode t1, TNode t2);

  void sendLemma( std::vector< Node >& ant, Node conc, const char * c, bool infer = false );
  void doPendingFacts();
public:
  eq::EqualityEngine* getEqualityEngine() {
    return &d_equalityEngine;
  }

  void initializeBounds();
};/* class TheorySep */

}/* CVC4::theory::sep namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SEP__THEORY_SEP_H */
