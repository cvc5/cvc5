/*********************                                                        */
/*! \file theory_strings.h
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
#include "theory/strings/theory_strings_preprocess.h"
#include "theory/strings/regexp_operation.h"

#include "context/cdchunk_list.h"
#include "context/cdhashset.h"

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
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

public:
  TheoryStrings(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo);
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
  /**
   * Function symbol used to implement uninterpreted undefined string
   * semantics.  Needed to deal with partial charat/substr function.
   */
  Node d_ufSubstr;

  // Constants
  Node d_emptyString;
  Node d_emptyRegexp;
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
  // Options
  bool d_opt_fmf;
  bool d_opt_regexp_gcd;
  // Helper functions
  Node getRepresentative( Node t );
  bool hasTerm( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  Node getLengthTerm( Node t );
  Node getLength( Node t );

private:
  /** The notify class */
  NotifyClass d_notify;
  /** Equaltity engine */
  eq::EqualityEngine d_equalityEngine;
  /** Are we in conflict */
  context::CDO<bool> d_conflict;
  //list of pairs of nodes to merge
  std::map< Node, Node > d_pending_exp;
  std::vector< Node > d_pending;
  std::vector< Node > d_lemma_cache;
  std::map< Node, bool > d_pending_req_phase;
  /** inferences */
  NodeList d_infer;
  NodeList d_infer_exp;
  /** normal forms */
  std::map< Node, Node > d_normal_forms_base;
  std::map< Node, std::vector< Node > > d_normal_forms;
  std::map< Node, std::vector< Node > > d_normal_forms_exp;
  //map of pairs of terms that have the same normal form
  NodeListMap d_nf_pairs;
  void addNormalFormPair( Node n1, Node n2 );
  bool isNormalFormPair( Node n1, Node n2 );
  bool isNormalFormPair2( Node n1, Node n2 );
  // loop ant
  NodeSet d_loop_antec;
  NodeSet d_length_intro_vars;
  // preReg cache
  NodeSet d_prereg_cached;

  /////////////////////////////////////////////////////////////////////////////
  // MODEL GENERATION
  /////////////////////////////////////////////////////////////////////////////
public:
  void collectModelInfo(TheoryModel* m, bool fullModel);

  /////////////////////////////////////////////////////////////////////////////
  // NOTIFICATIONS
  /////////////////////////////////////////////////////////////////////////////
public:
  void presolve();
  void shutdown() { }

  /////////////////////////////////////////////////////////////////////////////
  // MAIN SOLVER
  /////////////////////////////////////////////////////////////////////////////
private:
  void addSharedTerm(TNode n);
  EqualityStatus getEqualityStatus(TNode a, TNode b);

private:
  class EqcInfo {
  public:
    EqcInfo( context::Context* c );
    ~EqcInfo(){}
    //constant in this eqc
    context::CDO< Node > d_const_term;
    context::CDO< Node > d_length_term;
    context::CDO< unsigned > d_cardinality_lem_k;
    // 1 = added length lemma
    context::CDO< Node > d_normalized_length;
  };
  /** map from representatives to information necessary for equivalence classes */
  std::map< Node, EqcInfo* > d_eqc_info;
  EqcInfo * getOrMakeEqcInfo( Node eqc, bool doMake = true );
  //maintain which concat terms have the length lemma instantiated
  NodeSet d_length_nodes;
  NodeNodeMap d_length_inst;
private:
  void mergeCstVec(std::vector< Node > &vec_strings);
  bool getNormalForms(Node &eqc, std::vector< Node > & visited, std::vector< Node > & nf,
        std::vector< std::vector< Node > > &normal_forms,
        std::vector< std::vector< Node > > &normal_forms_exp,
        std::vector< Node > &normal_form_src);
  bool detectLoop(std::vector< std::vector< Node > > &normal_forms,
        int i, int j, int index_i, int index_j,
        int &loop_in_i, int &loop_in_j);
  bool processLoop(std::vector< Node > &antec,
        std::vector< std::vector< Node > > &normal_forms,
        std::vector< Node > &normal_form_src,
        int i, int j, int loop_n_index, int other_n_index,
        int loop_index, int index, int other_index);
  bool processNEqc(std::vector< std::vector< Node > > &normal_forms,
        std::vector< std::vector< Node > > &normal_forms_exp,
        std::vector< Node > &normal_form_src);
  bool processReverseNEq(std::vector< std::vector< Node > > &normal_forms,
        std::vector< Node > &normal_form_src, std::vector< Node > &curr_exp, unsigned i, unsigned j );
  bool processSimpleNEq( std::vector< std::vector< Node > > &normal_forms,
        std::vector< Node > &normal_form_src, std::vector< Node > &curr_exp, unsigned i, unsigned j,
        unsigned& index_i, unsigned& index_j, bool isRev );
  bool normalizeEquivalenceClass( Node n, std::vector< Node > & visited, std::vector< Node > & nf, std::vector< Node > & nf_exp );
  bool processDeq( Node n1, Node n2 );
  int processReverseDeq( std::vector< Node >& nfi, std::vector< Node >& nfj, Node ni, Node nj );
  int processSimpleDeq( std::vector< Node >& nfi, std::vector< Node >& nfj, Node ni, Node nj, unsigned& index, bool isRev );
  //bool unrollStar( Node atom );
  Node mkRegExpAntec(Node atom, Node ant);

  bool checkSimple();
  bool checkNormalForms();
  void checkDeqNF();
  bool checkLengthsEqc();
  bool checkCardinality();
  bool checkInductiveEquations();
  bool checkMemberships();
  bool checkPDerivative(Node x, Node r, Node atom, bool &addedLemma,
    std::vector< Node > &processed, std::vector< Node > &cprocessed,
    std::vector< Node > &nf_exp);
  bool checkContains();
  bool checkPosContains();
  bool checkNegContains();

public:
  void preRegisterTerm(TNode n);
  Node expandDefinition(LogicRequest &logicRequest, Node n);
  void check(Effort e);

  /** Conflict when merging two constants */
  void conflict(TNode a, TNode b);
  /** called when a new equivalence class is created */
  void eqNotifyNewClass(TNode t);
  /** called when two equivalence classes will merge */
  void eqNotifyPreMerge(TNode t1, TNode t2);
  /** called when two equivalence classes have merged */
  void eqNotifyPostMerge(TNode t1, TNode t2);
  /** called when two equivalence classes are made disequal */
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
protected:
  /** compute care graph */
  void computeCareGraph();

  //do pending merges
  void doPendingFacts();
  void doPendingLemmas();

  void sendLemma( Node ant, Node conc, const char * c );
  void sendInfer( Node eq_exp, Node eq, const char * c );
  void sendSplit( Node a, Node b, const char * c, bool preq = true );
  /** mkConcat **/
  inline Node mkConcat( Node n1, Node n2 );
  inline Node mkConcat( std::vector< Node >& c );
  /** mkExplain **/
  Node mkExplain( std::vector< Node >& a );
  Node mkExplain( std::vector< Node >& a, std::vector< Node >& an );
  /** mkAnd **/
  Node mkAnd( std::vector< Node >& a );
  /** get concat vector */
  void getConcatVec( Node n, std::vector< Node >& c );

  //get equivalence classes
  void getEquivalenceClasses( std::vector< Node >& eqcs );
  //get final normal form
  void getFinalNormalForm( Node n, std::vector< Node >& nf, std::vector< Node >& exp );

  //separate into collections with equal length
  void separateByLength( std::vector< Node >& n, std::vector< std::vector< Node > >& col, std::vector< Node >& lts );
  void printConcat( std::vector< Node >& n, const char * c );

private:
  Node mkSplitEq( const char * c, const char * info, Node lhs, Node rhs, bool lgtZero );

  // Special String Functions
  NodeList d_str_pos_ctn;
  NodeList d_str_neg_ctn;
  NodeSet d_neg_ctn_eqlen;
  NodeSet d_neg_ctn_ulen;
  NodeSet d_pos_ctn_cached;
  NodeSet d_neg_ctn_cached;

  // Symbolic Regular Expression
private:
  // regular expression memberships
  NodeList d_regexp_memberships;
  NodeSet d_regexp_ucached;
  NodeSet d_regexp_ccached;
  // intersection
  NodeListMap d_str_re_map;
  NodeNodeMap d_inter_cache;
  NodeIntMap d_inter_index;
  // antecedant for why regexp membership must be true
  NodeNodeMap d_regexp_ant;
  // membership length
  //std::map< Node, bool > d_membership_length;
  // regular expression operations
  RegExpOpr d_regexp_opr;

  CVC4::String getHeadConst( Node x );
  bool deriveRegExp( Node x, Node r, Node ant );
  bool addMembershipLength(Node atom);
  void addMembership(Node assertion);
  Node getNormalString(Node x, std::vector<Node> &nf_exp);
  Node getNormalSymRegExp(Node r, std::vector<Node> &nf_exp);


  // Finite Model Finding
private:
  NodeSet d_input_vars;
  context::CDO< Node > d_input_var_lsum;
  context::CDHashMap< int, Node > d_cardinality_lits;
  context::CDO< int > d_curr_cardinality;
public:
  //for finite model finding
  Node getNextDecisionRequest();
  void assertNode( Node lit );

public:
/** statistics class */
  class Statistics {
  public:
    IntStat d_splits;
    IntStat d_eq_splits;
    IntStat d_deq_splits;
    IntStat d_loop_lemmas;
    IntStat d_new_skolems;
    Statistics();
    ~Statistics();
  };/* class TheoryStrings::Statistics */
  Statistics d_statistics;
};/* class TheoryStrings */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__THEORY_STRINGS_H */
