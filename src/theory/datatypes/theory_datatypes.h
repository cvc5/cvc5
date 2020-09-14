/*********************                                                        */
/*! \file theory_datatypes.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory of datatypes.
 **
 ** Theory of datatypes.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H
#define CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H

#include <iostream>
#include <map>

#include "context/cdlist.h"
#include "expr/attribute.h"
#include "expr/node_trie.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/datatypes/inference_manager.h"
#include "theory/datatypes/sygus_extension.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"
#include "util/hash.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

class TheoryDatatypes : public Theory {
 private:
  typedef context::CDList<Node> NodeList;
  /** maps nodes to an index in a vector */
  typedef context::CDHashMap<Node, size_t, NodeHashFunction> NodeUIntMap;
  typedef context::CDHashMap<Node, bool, NodeHashFunction> BoolMap;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeMap;

  Node d_true;
  Node d_zero;
  /** mkAnd */
  Node mkAnd(std::vector<TNode>& assumptions);

 private:
  //notification class for equality engine
  class NotifyClass : public eq::EqualityEngineNotify {
    TheoryDatatypes& d_dt;
  public:
    NotifyClass(TheoryDatatypes& dt): d_dt(dt) {}
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override
    {
      Debug("dt") << "NotifyClass::eqNotifyTriggerPredicate(" << predicate << ", " << (value ? "true" : "false") << ")" << std::endl;
      if (value) {
        return d_dt.propagateLit(predicate);
      }
      return d_dt.propagateLit(predicate.notNode());
    }
    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override
    {
      AlwaysAssert(tag == THEORY_DATATYPES);
      Debug("dt") << "NotifyClass::eqNotifyTriggerTermMerge(" << tag << ", " << t1 << ", " << t2 << ")" << std::endl;
      if (value) {
        return d_dt.propagateLit(t1.eqNode(t2));
      }
      return d_dt.propagateLit(t1.eqNode(t2).notNode());
    }
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override
    {
      Debug("dt") << "NotifyClass::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << ")" << std::endl;
      d_dt.conflict(t1, t2);
    }
    void eqNotifyNewClass(TNode t) override
    {
      Debug("dt") << "NotifyClass::eqNotifyNewClass(" << t << ")" << std::endl;
      d_dt.eqNotifyNewClass(t);
    }
    void eqNotifyMerge(TNode t1, TNode t2) override
    {
      Debug("dt") << "NotifyClass::eqNotifyMerge(" << t1 << ", " << t2 << ")"
                  << std::endl;
      d_dt.eqNotifyMerge(t1, t2);
    }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override
    {
    }
  };/* class TheoryDatatypes::NotifyClass */
private:
  /** equivalence class info
   * d_inst is whether the instantiate rule has been applied,
   * d_constructor is a node of kind APPLY_CONSTRUCTOR (if any) in this equivalence class,
   * d_selectors is whether a selector has been applied to this equivalence class.
   */
  class EqcInfo
  {
  public:
    EqcInfo( context::Context* c );
    ~EqcInfo(){}
    //whether we have instantiatied this eqc
    context::CDO< bool > d_inst;
    //constructor equal to this eqc
    context::CDO< Node > d_constructor;
    //all selectors whose argument is this eqc
    context::CDO< bool > d_selectors;
  };
  /** does eqc of n have a label (do we know its constructor)? */
  bool hasLabel( EqcInfo* eqc, Node n );
  /** get the label associated to n */
  Node getLabel( Node n );
  /** get the index of the label associated to n */
  int getLabelIndex( EqcInfo* eqc, Node n );
  /** does eqc of n have any testers? */
  bool hasTester( Node n );
  /** get the possible constructors for n */
  void getPossibleCons( EqcInfo* eqc, Node n, std::vector< bool >& cons );
  /** mkExpDefSkolem */
  void mkExpDefSkolem( Node sel, TypeNode dt, TypeNode rt );
  /** skolems for terms */
  NodeMap d_term_sk;
  Node getTermSkolemFor( Node n );
private:
  /** The notify class */
  NotifyClass d_notify;
  /** information necessary for equivalence classes */
  std::map< Node, EqcInfo* > d_eqc_info;
  /** map from nodes to their instantiated equivalent for each constructor type */
  std::map< Node, std::map< int, Node > > d_inst_map;
  //---------------------------------labels
  /** labels for each equivalence class
   *
   * For each eqc r, d_labels[r] is testers that hold for this equivalence
   * class, either:
   * a list of equations of the form
   *   NOT is_[constructor_1]( t1 )...NOT is_[constructor_n]( tn ), each of
   *   which are unique testers, n is less than the number of possible
   *   constructors for t minus one,
   * or a list of equations of the form
   *   NOT is_[constructor_1]( t1 )...NOT is_[constructor_n]( tn ) followed by
   *   is_[constructor_(n+1)]( t{n+1} ), each of which is a unique tester.
   * In both cases, t1, ..., tn, t{n+1} are terms in the equivalence class of r.
   *
   * We store this list in a context-dependent way, using the four data
   * structures below. The three vectors d_labels_data, d_labels_args, and
   * d_labels_tindex store the tester applications, their arguments and the
   * tester index of the application. The map d_labels stores the number of
   * values in these vectors that is valid in the current context (this is an
   * optimization that ensures we don't need to pop data when changing SAT
   * contexts).
   */
  NodeUIntMap d_labels;
  /** the tester applications */
  std::map< Node, std::vector< Node > > d_labels_data;
  /** the argument of each node in d_labels_data */
  std::map<Node, std::vector<Node> > d_labels_args;
  /** the tester index of each node in d_labels_data */
  std::map<Node, std::vector<unsigned> > d_labels_tindex;
  //---------------------------------end labels
  /** selector apps for eqch equivalence class */
  NodeUIntMap d_selector_apps;
  std::map< Node, std::vector< Node > > d_selector_apps_data;
  /** The conflict node */
  Node d_conflictNode;
  /**
   * SAT-context dependent cache for which terms we have called
   * collectTerms(...) on.
   */
  BoolMap d_collectTermsCache;
  /**
   * User-context dependent cache for which terms we have called
   * collectTerms(...) on.
   */
  BoolMap d_collectTermsCacheU;
  /** All the function terms that the theory has seen */
  context::CDList<TNode> d_functionTerms;
  /** counter for forcing assignments (ensures fairness) */
  unsigned d_dtfCounter;
  /** expand definition skolem functions */
  std::map< TypeNode, std::map< Node, Node > > d_exp_def_skolem;
  /** uninterpreted constant to variable map */
  std::map< Node, Node > d_uc_to_fresh_var;
private:
  /** singleton lemmas (for degenerate co-datatype case) */
  std::map< TypeNode, Node > d_singleton_lemma[2];
  /** Cache for singleton equalities processed */
  BoolMap d_singleton_eq;
  /** list of all lemmas produced */
  BoolMap d_lemmas_produced_c;
private:
  /** assert fact */
  void assertFact( Node fact, Node exp );

  /** get or make eqc info */
  EqcInfo* getOrMakeEqcInfo( TNode n, bool doMake = false );

  /** has eqc info */
  bool hasEqcInfo( TNode n ) { return d_labels.find( n )!=d_labels.end(); }

  /** get eqc constructor */
  TNode getEqcConstructor( TNode r );

 protected:
  void addCarePairs(TNodeTrie* t1,
                    TNodeTrie* t2,
                    unsigned arity,
                    unsigned depth,
                    unsigned& n_pairs);
  /** compute care graph */
  void computeCareGraph() override;

 public:
  TheoryDatatypes(context::Context* c,
                  context::UserContext* u,
                  OutputChannel& out,
                  Valuation valuation,
                  const LogicInfo& logicInfo,
                  ProofNodeManager* pnm = nullptr);
  ~TheoryDatatypes();

  //--------------------------------- initialization
  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /**
   * Returns true if we need an equality engine. If so, we initialize the
   * information regarding how it should be setup. For details, see the
   * documentation in Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi) override;
  /** finish initialization */
  void finishInit() override;
  //--------------------------------- end initialization
  /** propagate */
  bool propagateLit(TNode literal);
  /** Conflict when merging two constants */
  void conflict(TNode a, TNode b);
  /** explain */
  void addAssumptions( std::vector<TNode>& assumptions, std::vector<TNode>& tassumptions );
  void explainEquality( TNode a, TNode b, bool polarity, std::vector<TNode>& assumptions );
  void explainPredicate( TNode p, bool polarity, std::vector<TNode>& assumptions );
  void explain( TNode literal, std::vector<TNode>& assumptions );
  TrustNode explain(TNode literal) override;
  Node explainLit(TNode literal);
  Node explain( std::vector< Node >& lits );
  /** called when a new equivalance class is created */
  void eqNotifyNewClass(TNode t);
  /** called when two equivalance classes have merged */
  void eqNotifyMerge(TNode t1, TNode t2);

  //--------------------------------- standard check
  /** Do we need a check call at last call effort? */
  bool needsCheckLastEffort() override;
  /** Pre-check, called before the fact queue of the theory is processed. */
  bool preCheck(Effort level) override;
  /** Post-check, called after the fact queue of the theory is processed. */
  void postCheck(Effort level) override;
  /** Notify fact */
  void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) override;
  //--------------------------------- end standard check
  void preRegisterTerm(TNode n) override;
  TrustNode expandDefinition(Node n) override;
  TrustNode ppRewrite(TNode n) override;
  EqualityStatus getEqualityStatus(TNode a, TNode b) override;
  std::string identify() const override
  {
    return std::string("TheoryDatatypes");
  }
  /** debug print */
  void printModelDebug( const char* c );
  /** entailment check */
  std::pair<bool, Node> entailmentCheck(TNode lit) override;

 private:
  /** add tester to equivalence class info */
  void addTester(unsigned ttindex, Node t, EqcInfo* eqc, Node n, Node t_arg);
  /** add selector to equivalence class info */
  void addSelector( Node s, EqcInfo* eqc, Node n, bool assertFacts = true );
  /** add constructor */
  void addConstructor( Node c, EqcInfo* eqc, Node n );
  /** merge the equivalence class info of t1 and t2 */
  void merge( Node t1, Node t2 );
  /** collapse selector, s is of the form sel( n ) where n = c */
  void collapseSelector( Node s, Node c );
  /** remove uninterpreted constants */
  Node removeUninterpretedConstants( Node n, std::map< Node, Node >& visited );
  /** for checking if cycles exist */
  void checkCycles();
  Node searchForCycle(TNode n,
                      TNode on,
                      std::map<TNode, bool>& visited,
                      std::map<TNode, bool>& proc,
                      std::vector<Node>& explanation,
                      bool firstTime = true);
  /** for checking whether two codatatype terms must be equal */
  void separateBisimilar( std::vector< Node >& part, std::vector< std::vector< Node > >& part_out,
                          std::vector< TNode >& exp,
                          std::map< Node, Node >& cn,
                          std::map< Node, std::map< Node, int > >& dni, int dniLvl, bool mkExp );
  /** build model */
  Node getCodatatypesValue( Node n, std::map< Node, Node >& eqc_cons, std::map< Node, int >& vmap, int depth );
  /** get singleton lemma */
  Node getSingletonLemma( TypeNode tn, bool pol );
  /** collect terms */
  void collectTerms( Node n );
  /** get instantiate cons */
  Node getInstantiateCons(Node n, const DType& dt, int index);
  /** check instantiate */
  void instantiate( EqcInfo* eqc, Node n );
private:
  //equality queries
  bool hasTerm( TNode a );
  bool areEqual( TNode a, TNode b );
  bool areDisequal( TNode a, TNode b );
  bool areCareDisequal( TNode x, TNode y );
  TNode getRepresentative( TNode a );

  /** Collect model values in m based on the relevant terms given by termSet */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;
  /**
   * Compute relevant terms. This includes datatypes in non-singleton
   * equivalence classes.
   */
  void computeRelevantTerms(std::set<Node>& termSet) override;

  /** sygus symmetry breaking utility */
  std::unique_ptr<SygusExtension> d_sygusExtension;

  /** The theory rewriter for this theory. */
  DatatypesRewriter d_rewriter;
  /** A (default) theory state object */
  TheoryState d_state;
  /** The inference manager */
  InferenceManager d_im;
};/* class TheoryDatatypes */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H */
