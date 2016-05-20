/*********************                                                        */
/*! \file theory_strings.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
#include "expr/attribute.h"

#include <climits>
#include <deque>

namespace CVC4 {
namespace theory {

namespace quantifiers{
  class TermArgTrie;
}

namespace strings {

/**
 * Decision procedure for strings.
 *
 */

struct StringsProxyVarAttributeId {};
typedef expr::Attribute< StringsProxyVarAttributeId, bool > StringsProxyVarAttribute;

class TheoryStrings : public Theory {
  typedef context::CDChunkList<Node> NodeList;
  typedef context::CDHashMap<Node, NodeList*, NodeHashFunction> NodeListMap;
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

public:
  TheoryStrings(context::Context* c, context::UserContext* u,
                OutputChannel& out, Valuation valuation,
                const LogicInfo& logicInfo);
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
  // Constants
  Node d_emptyString;
  Node d_emptyRegexp;
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
  CVC4::Rational RMAXINT;
  unsigned d_card_size;
  // Helper functions
  Node getRepresentative( Node t );
  bool hasTerm( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  // t is representative, te = t, add lt = te to explanation exp
  Node getLengthExp( Node t, std::vector< Node >& exp, Node te );
  Node getLength( Node t, std::vector< Node >& exp );

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
  /** inferences: maintained to ensure ref count for internally introduced nodes */
  NodeList d_infer;
  NodeList d_infer_exp;
  /** normal forms */
  std::map< Node, Node > d_normal_forms_base;
  std::map< Node, std::vector< Node > > d_normal_forms;
  std::map< Node, std::vector< Node > > d_normal_forms_exp;
  std::map< Node, std::map< Node, std::map< bool, int > > > d_normal_forms_exp_depend;
  //map of pairs of terms that have the same normal form
  NodeListMap d_nf_pairs;
  void addNormalFormPair( Node n1, Node n2 );
  bool isNormalFormPair( Node n1, Node n2 );
  bool isNormalFormPair2( Node n1, Node n2 );
  // loop ant
  NodeSet d_loop_antec;
  NodeSet d_length_intro_vars;
  // preReg cache
  NodeSet d_pregistered_terms_cache;
  NodeSet d_registered_terms_cache;
  // preprocess cache
  StringsPreprocess d_preproc;
  NodeBoolMap d_preproc_cache;
  // extended functions inferences cache
  NodeSet d_extf_infer_cache;
  std::vector< Node > d_empty_vec;
  //
  NodeList d_ee_disequalities;
private:
  NodeSet d_congruent;
  std::map< Node, Node > d_eqc_to_const;
  std::map< Node, Node > d_eqc_to_const_base;
  std::map< Node, Node > d_eqc_to_const_exp;
  std::map< Node, Node > d_eqc_to_len_term;
  std::vector< Node > d_strings_eqc;
  Node d_emptyString_r;
  class TermIndex {
  public:
    Node d_data;
    std::map< Node, TermIndex > d_children;
    Node add( Node n, unsigned index, TheoryStrings* t, Node er, std::vector< Node >& c );
    void clear(){ d_children.clear(); }
  };
  std::map< Kind, TermIndex > d_term_index;
  //list of non-congruent concat terms in each eqc
  std::map< Node, std::vector< Node > > d_eqc;
  std::map< Node, std::vector< Node > > d_flat_form;
  std::map< Node, std::vector< int > > d_flat_form_index;

  void debugPrintFlatForms( const char * tc );
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
  NodeNodeMap d_proxy_var;
  NodeNodeMap d_proxy_var_to_length;
  /** All the function terms that the theory has seen */
  context::CDList<TNode> d_functionsTerms;
private:
  //initial check
  void checkInit();
  void checkConstantEquivalenceClasses( TermIndex* ti, std::vector< Node >& vecc );
  //extended functions evaluation check
  void checkExtendedFuncsEval( int effort = 0 );
  void checkExtfInference( Node n, Node nr, int effort );
  void collectVars( Node n, std::map< Node, std::vector< Node > >& vars, std::map< Node, bool >& visited );
  Node getSymbolicDefinition( Node n, std::vector< Node >& exp );
  //check extf reduction
  void checkExtfReduction( int effort );
  void checkReduction( Node atom, int pol, int effort );
  //flat forms check
  void checkFlatForms();
  Node checkCycles( Node eqc, std::vector< Node >& curr, std::vector< Node >& exp );
  //normal forms check
  void checkNormalForms();
  bool normalizeEquivalenceClass( Node n, std::vector< Node > & nf, std::vector< Node > & nf_exp );
  bool getNormalForms( Node &eqc, std::vector< std::vector< Node > > &normal_forms, std::vector< Node > &normal_form_src,
                       std::vector< std::vector< Node > > &normal_forms_exp, std::vector< std::map< Node, std::map< bool, int > > >& normal_forms_exp_depend);
  bool detectLoop(std::vector< std::vector< Node > > &normal_forms,
        int i, int j, int index, int &loop_in_i, int &loop_in_j);
  bool processLoop(std::vector< Node > &antec,
        std::vector< std::vector< Node > > &normal_forms,
        std::vector< Node > &normal_form_src,
        int i, int j, int loop_n_index, int other_n_index,
        int loop_index, int index);
  bool processNEqc( std::vector< std::vector< Node > > &normal_forms, std::vector< Node > &normal_form_src,
                    std::vector< std::vector< Node > > &normal_forms_exp, std::vector< std::map< Node, std::map< bool, int > > >& normal_forms_exp_depend );
  bool processReverseNEq( std::vector< std::vector< Node > > &normal_forms, std::vector< Node > &normal_form_src, 
                          std::vector< std::vector< Node > > &normal_forms_exp, std::vector< std::map< Node, std::map< bool, int > > >& normal_forms_exp_depend, 
                          unsigned i, unsigned j );
  bool processSimpleNEq( std::vector< std::vector< Node > > &normal_forms, std::vector< Node > &normal_form_src, 
                         std::vector< std::vector< Node > > &normal_forms_exp, std::vector< std::map< Node, std::map< bool, int > > >& normal_forms_exp_depend, 
                         unsigned i, unsigned j, unsigned& index, bool isRev );
  bool processDeq( Node n1, Node n2 );
  int processReverseDeq( std::vector< Node >& nfi, std::vector< Node >& nfj, Node ni, Node nj );
  int processSimpleDeq( std::vector< Node >& nfi, std::vector< Node >& nfj, Node ni, Node nj, unsigned& index, bool isRev );
  void checkDeqNF();
  
  void getExplanationVectorForPrefix( std::vector< std::vector< Node > > &normal_forms, std::vector< Node > &normal_form_src,
                                      std::vector< std::vector< Node > > &normal_forms_exp, std::vector< std::map< Node, std::map< bool, int > > >& normal_forms_exp_depend,
                                      unsigned i, unsigned j, int index, bool isRev, std::vector< Node >& curr_exp );

  //check for extended functions
  void checkExtendedFuncs();
  //check membership constraints
  Node mkRegExpAntec(Node atom, Node ant);
  Node normalizeRegexp(Node r);
  bool normalizePosMemberships( std::map< Node, std::vector< Node > > &memb_with_exps );
  bool applyRConsume( CVC4::String &s, Node &r );
  Node applyRSplit( Node s1, Node s2, Node r );
  bool applyRLen( std::map< Node, std::vector< Node > > &XinR_with_exps );
  bool checkMembershipsWithoutLength( std::map< Node, std::vector< Node > > &memb_with_exps, 
                                      std::map< Node, std::vector< Node > > &XinR_with_exps);
  void checkMemberships();
  bool checkMemberships2();
  bool checkPDerivative( Node x, Node r, Node atom, bool &addedLemma,
                         std::vector< Node > &processed, std::vector< Node > &cprocessed,
                         std::vector< Node > &nf_exp);
  //check contains
  void checkPosContains( std::vector< Node >& posContains );
  void checkNegContains( std::vector< Node >& negContains );
  //lengths normalize check
  void checkLengthsEqc();
  //cardinality check
  void checkCardinality();

private:
  void addCarePairs( quantifiers::TermArgTrie * t1, quantifiers::TermArgTrie * t2, unsigned arity, unsigned depth );
public:
  /** preregister term */
  void preRegisterTerm(TNode n);
  /** Expand definition */
  Node expandDefinition(LogicRequest &logicRequest, Node n);
  /** Check at effort e */
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
  /** get preprocess */
  StringsPreprocess * getPreprocess() { return &d_preproc; }
protected:
  /** compute care graph */
  void computeCareGraph();

  //do pending merges
  void assertPendingFact(Node atom, bool polarity, Node exp);
  void doPendingFacts();
  void doPendingLemmas();
  bool hasProcessed();
  void addToExplanation( Node a, Node b, std::vector< Node >& exp );
  void addToExplanation( Node lit, std::vector< Node >& exp );

  //register term
  void registerTerm( Node n, int effort );
  //send lemma
  void sendInference( std::vector< Node >& exp, std::vector< Node >& exp_n, Node eq, const char * c, bool asLemma = false );
  void sendInference( std::vector< Node >& exp, Node eq, const char * c, bool asLemma = false );
  void sendLemma( Node ant, Node conc, const char * c );
  void sendInfer( Node eq_exp, Node eq, const char * c );
  void sendSplit( Node a, Node b, const char * c, bool preq = true );
  void sendLengthLemma( Node n );
  /** mkConcat **/
  inline Node mkConcat( Node n1, Node n2 );
  inline Node mkConcat( Node n1, Node n2, Node n3 );
  inline Node mkConcat( const std::vector< Node >& c );
  inline Node mkLength( Node n );
  //mkSkolem
  enum {
    sk_id_c_spt,
    sk_id_vc_spt,
    sk_id_v_spt,
    sk_id_ctn_pre,
    sk_id_ctn_post,
    sk_id_deq_x,
    sk_id_deq_y,
    sk_id_deq_z,
  };
  std::map< Node, std::map< Node, std::map< int, Node > > > d_skolem_cache;
  Node mkSkolemCached( Node a, Node b, int id, const char * c, int isLenSplit = 0 );
  inline Node mkSkolemS(const char * c, int isLenSplit = 0);
  //inline Node mkSkolemI(const char * c);
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

  void inferSubstitutionProxyVars( Node n, std::vector< Node >& vars, std::vector< Node >& subs, std::vector< Node >& unproc );
private:

  // Special String Functions
  NodeSet d_neg_ctn_eqlen;
  NodeSet d_neg_ctn_ulen;
  NodeSet d_neg_ctn_cached;
  //extended string terms and whether they have been reduced
  NodeBoolMap d_ext_func_terms;
  std::map< Node, std::map< Node, std::vector< Node > > > d_extf_vars;
  // list of terms that something (does not) contain and their explanation
  class ExtfInfo {
  public:
    std::map< bool, std::vector< Node > > d_ctn;
    std::map< bool, std::vector< Node > > d_ctn_from;
  };
  std::map< Node, int > d_extf_pol;
  std::map< Node, std::vector< Node > > d_extf_exp;
  std::map< Node, ExtfInfo > d_extf_info;
  //collect extended operator terms
  void collectExtendedFuncTerms( Node n, std::map< Node, bool >& visited );

  // Symbolic Regular Expression
private:
  // regular expression memberships
  NodeList d_regexp_memberships;
  NodeSet d_regexp_ucached;
  NodeSet d_regexp_ccached;
  // stored assertions
  NodeListMap d_pos_memberships;
  NodeListMap d_neg_memberships;
  // semi normal forms for symbolic expression
  std::map< Node, Node > d_nf_regexps;
  std::map< Node, std::vector< Node > > d_nf_regexps_exp;
  // intersection
  NodeNodeMap d_inter_cache;
  NodeIntMap d_inter_index;
  // processed memberships
  NodeSet d_processed_memberships;
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
