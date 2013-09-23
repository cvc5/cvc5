/*********************                                                        */
/*! \file theory_strings.h
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2013-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of strings
 **
 ** Theory of strings.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__STRINGS__THEORY_STRINGS_H
#define __CVC4__THEORY__STRINGS__THEORY_STRINGS_H

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

#include "context/cdchunk_list.h"

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * Decision procedure for strings.
 *
 */

class TheoryStrings : public Theory {
  typedef context::CDChunkList<Node> NodeList;
  typedef context::CDHashMap<Node, NodeList*, NodeHashFunction> NodeListMap;
  public:

  TheoryStrings(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe);
  ~TheoryStrings();

  void setMasterEqualityEngine(eq::EqualityEngine* eq);

  std::string identify() const { return std::string("TheoryStrings"); }


  public:

  void propagate(Effort e);
  bool propagate(TNode literal);
  void explain( TNode literal, std::vector<TNode>& assumptions );
  Node explain( TNode literal );


  // NotifyClass for equality engine
  class NotifyClass : public eq::EqualityEngineNotify {
    TheoryStrings& d_str;
  public:
    NotifyClass(TheoryStrings& t_str): d_str(t_str) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value) {
      Debug("strings") << "NotifyClass::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false" )<< ")" << std::endl;
      if (value) {
        return d_str.propagate(equality);
      } else {
        // We use only literal triggers so taking not is safe
        return d_str.propagate(equality.notNode());
      }
    }
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) {
      Debug("strings") << "NotifyClass::eqNotifyTriggerPredicate(" << predicate << ", " << (value ? "true" : "false") << ")" << std::endl;
      if (value) {
        return d_str.propagate(predicate);
      } else {
       return d_str.propagate(predicate.notNode());
      }
    }
    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
      Debug("strings") << "NotifyClass::eqNotifyTriggerTermMerge(" << tag << ", " << t1 << ", " << t2 << ")" << std::endl;
      if (value) {
        return d_str.propagate(t1.eqNode(t2));
      } else {
        return d_str.propagate(t1.eqNode(t2).notNode());
      }
    }
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) {
      Debug("strings") << "NotifyClass::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << ")" << std::endl;
      d_str.conflict(t1, t2);
    }
    void eqNotifyNewClass(TNode t) {
      Debug("strings") << "NotifyClass::eqNotifyNewClass(" << t << std::endl;
      d_str.eqNotifyNewClass(t);
    }
    void eqNotifyPreMerge(TNode t1, TNode t2) {
      Debug("strings") << "NotifyClass::eqNotifyPreMerge(" << t1 << ", " << t2 << std::endl;
      d_str.eqNotifyPreMerge(t1, t2);
    }
    void eqNotifyPostMerge(TNode t1, TNode t2) {
      Debug("strings") << "NotifyClass::eqNotifyPostMerge(" << t1 << ", " << t2 << std::endl;
      d_str.eqNotifyPostMerge(t1, t2);
    }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {
      Debug("strings") << "NotifyClass::eqNotifyDisequal(" << t1 << ", " << t2 << ", " << reason << std::endl;
      d_str.eqNotifyDisequal(t1, t2, reason);
    }
  };/* class TheoryStrings::NotifyClass */

  private:
    /** The notify class */
    NotifyClass d_notify;
    /** Equaltity engine */
    eq::EqualityEngine d_equalityEngine;
    /** Are we in conflict */
    context::CDO<bool> d_conflict;
	std::vector< Node > d_length_intro_vars;
    Node d_emptyString;
    Node d_true;
    Node d_false;
    Node d_zero;
    //list of pairs of nodes to merge
      std::map< Node, Node > d_pending_exp;
      std::vector< Node > d_pending;
      std::vector< Node > d_lemma_cache;
  bool hasTerm( Node a );
  bool areEqual( Node a, Node b );
  /** inferences */
  NodeList d_infer;
  NodeList d_infer_exp;
  //map of pairs of terms that have the same normal form
  NodeListMap d_nf_pairs;
  void addNormalFormPair( Node n1, Node n2 );
  bool isNormalFormPair( Node n1, Node n2 );
  bool isNormalFormPair2( Node n1, Node n2 );

  NodeListMap d_ind_map1;
  NodeListMap d_ind_map2;
  NodeListMap d_ind_map_exp;
  NodeListMap d_ind_map_lemma;
  void addInductiveEquation( Node x, Node y, Node z, Node exp );

  /////////////////////////////////////////////////////////////////////////////
  // MODEL GENERATION
  /////////////////////////////////////////////////////////////////////////////
  public:

  void collectModelInfo(TheoryModel* m, bool fullModel);

  /////////////////////////////////////////////////////////////////////////////
  // NOTIFICATIONS
  /////////////////////////////////////////////////////////////////////////////

  public:

  void shutdown() { }

  /////////////////////////////////////////////////////////////////////////////
  // MAIN SOLVER
  /////////////////////////////////////////////////////////////////////////////
  private:
  void dealPositiveWordEquation(TNode n);
  void addSharedTerm(TNode n);

  private:
  class EqcInfo
  {
  public:
    EqcInfo( context::Context* c );
    ~EqcInfo(){}
    //constant in this eqc
    context::CDO< Node > d_const_term;
    context::CDO< Node > d_length_term;
    context::CDO< unsigned > d_cardinality_lem_k;
  };
  /** map from representatives to information necessary for equivalence classes */
  std::map< Node, EqcInfo* > d_eqc_info;
  EqcInfo * getOrMakeEqcInfo( Node eqc, bool doMake = true );
  //maintain which concat terms have the length lemma instantiatied
  std::map< Node, bool > d_length_inst;
  private:
    std::map< Node, std::vector< Node > > d_normal_forms;
    std::map< Node, std::vector< Node > > d_normal_forms_exp;
    void getNormalForms(Node &eqc, std::vector< Node > & visited, std::vector< Node > & nf,
    std::vector< std::vector< Node > > &normal_forms,  std::vector< std::vector< Node > > &normal_forms_exp, std::vector< Node > &normal_form_src);
    void normalizeEquivalenceClass( Node n, std::vector< Node > & visited, std::vector< Node > & nf, std::vector< Node > & nf_exp );
    bool areLengthsEqual( Node n1, Node n2 ); //TODO

    bool checkNormalForms();
    bool checkCardinality();
    bool checkInductiveEquations();
	int gcd(int a, int b);
  public:
  void preRegisterTerm(TNode n);
  void check(Effort e);

  /** Conflict when merging two constants */
  void conflict(TNode a, TNode b);
  /** called when a new equivalance class is created */
  void eqNotifyNewClass(TNode t);
  /** called when two equivalance classes will merge */
  void eqNotifyPreMerge(TNode t1, TNode t2);
  /** called when two equivalance classes have merged */
  void eqNotifyPostMerge(TNode t1, TNode t2);
  /** called when two equivalence classes are made disequal */
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
protected:
  /** compute care graph */
  void computeCareGraph();

  //do pending merges
  void doPendingFacts();

  void sendLemma( Node ant, Node conc, const char * c );
  /** mkConcat **/
  Node mkConcat( std::vector< Node >& c );
  /** mkExplain **/
  Node mkExplain( std::vector< Node >& a, std::vector< Node >& an );

  //get final normal form
  void getFinalNormalForm( Node n, std::vector< Node >& nf, std::vector< Node >& exp );

  //seperate into collections with equal length
  void seperateIntoCollections( std::vector< Node >& n, std::vector< std::vector< Node > >& col, std::vector< Node >& lts );
};/* class TheoryStrings */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__THEORY_STRINGS_H */
