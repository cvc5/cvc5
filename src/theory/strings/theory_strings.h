/*********************                                                        */
/*! \file theory_strings.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
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

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "expr/attribute.h"
#include "theory/strings/regexp_operation.h"
#include "theory/strings/theory_strings_preprocess.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

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

/** Types of inferences used in the procedure
 *
 * These are variants of the inference rules in Figures 3-5 of Liang et al.
 * "A DPLL(T) Solver for a Theory of Strings and Regular Expressions", CAV 2014.
 */
enum Inference
{
  INFER_NONE,
  // string split constant propagation, for example:
  //     x = y, x = "abc", y = y1 ++ "b" ++ y2
  //       implies y1 = "a" ++ y1'
  INFER_SSPLIT_CST_PROP,
  // string split variable propagation, for example:
  //     x = y, x = x1 ++ x2, y = y1 ++ y2, len( x1 ) >= len( y1 )
  //       implies x1 = y1 ++ x1'
  // This is inspired by Zheng et al CAV 2015.
  INFER_SSPLIT_VAR_PROP,
  // length split, for example:
  //     len( x1 ) = len( y1 ) V len( x1 ) != len( y1 )
  // This is inferred when e.g. x = y, x = x1 ++ x2, y = y1 ++ y2.
  INFER_LEN_SPLIT,
  // length split empty, for example:
  //     z = "" V z != ""
  // This is inferred when, e.g. x = y, x = z ++ x1, y = y1 ++ z
  INFER_LEN_SPLIT_EMP,
  // string split constant binary, for example:
  //     x1 = "aaaa" ++ x1' V "aaaa" = x1 ++ x1'
  // This is inferred when, e.g. x = y, x = x1 ++ x2, y = "aaaaaaaa" ++ y2.
  // This inference is disabled by default and is enabled by stringBinaryCsp().
  INFER_SSPLIT_CST_BINARY,
  // string split constant
  //    x = y, x = "c" ++ x2, y = y1 ++ y2, y1 != ""
  //      implies y1 = "c" ++ y1'
  // This is a special case of F-Split in Figure 5 of Liang et al CAV 2014.
  INFER_SSPLIT_CST,
  // string split variable, for example:
  //    x = y, x = x1 ++ x2, y = y1 ++ y2
  //      implies x1 = y1 ++ x1' V y1 = x1 ++ y1'
  // This is rule F-Split in Figure 5 of Liang et al CAV 2014.
  INFER_SSPLIT_VAR,
  // flat form loop, for example:
  //    x = y, x = x1 ++ z, y = z ++ y2
  //      implies z = u2 ++ u1, u in ( u1 ++ u2 )*, x1 = u2 ++ u, y2 = u ++ u1
  //        for fresh u, u1, u2.
  // This is the rule F-Loop from Figure 5 of Liang et al CAV 2014.
  INFER_FLOOP,
};
std::ostream& operator<<(std::ostream& out, Inference i);

/** inference steps
 *
 * Corresponds to a step in the overall strategy of the strings solver. For
 * details on the individual steps, see documentation on the inference schemas
 * within TheoryStrings.
 */
enum InferStep
{
  // indicates that the strategy should break if lemmas or facts are added
  BREAK,
  // check initial
  CHECK_INIT,
  // check constant equivalence classes
  CHECK_CONST_EQC,
  // check extended function evaluation
  CHECK_EXTF_EVAL,
  // check cycles
  CHECK_CYCLES,
  // check flat forms
  CHECK_FLAT_FORMS,
  // check normal forms equalities
  CHECK_NORMAL_FORMS_EQ,
  // check normal forms disequalities
  CHECK_NORMAL_FORMS_DEQ,
  // check codes
  CHECK_CODES,
  // check lengths for equivalence classes
  CHECK_LENGTH_EQC,
  // check extended function reductions
  CHECK_EXTF_REDUCTION,
  // check regular expression memberships
  CHECK_MEMBERSHIP,
  // check cardinality
  CHECK_CARDINALITY,
};
std::ostream& operator<<(std::ostream& out, Inference i);

struct StringsProxyVarAttributeId {};
typedef expr::Attribute< StringsProxyVarAttributeId, bool > StringsProxyVarAttribute;

class TheoryStrings : public Theory {
  typedef context::CDList<Node> NodeList;
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  TheoryStrings(context::Context* c, context::UserContext* u,
                OutputChannel& out, Valuation valuation,
                const LogicInfo& logicInfo);
  ~TheoryStrings();

  void setMasterEqualityEngine(eq::EqualityEngine* eq) override;

  std::string identify() const override { return std::string("TheoryStrings"); }

 public:
  void propagate(Effort e) override;
  bool propagate(TNode literal);
  void explain( TNode literal, std::vector<TNode>& assumptions );
  Node explain(TNode literal) override;
  eq::EqualityEngine* getEqualityEngine() override { return &d_equalityEngine; }
  bool getCurrentSubstitution(int effort,
                              std::vector<Node>& vars,
                              std::vector<Node>& subs,
                              std::map<Node, std::vector<Node> >& exp) override;
  int getReduction(int effort, Node n, Node& nr) override;

  // NotifyClass for equality engine
  class NotifyClass : public eq::EqualityEngineNotify {
    TheoryStrings& d_str;
  public:
    NotifyClass(TheoryStrings& t_str): d_str(t_str) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value) override
    {
      Debug("strings") << "NotifyClass::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false" )<< ")" << std::endl;
      if (value) {
        return d_str.propagate(equality);
      } else {
        // We use only literal triggers so taking not is safe
        return d_str.propagate(equality.notNode());
      }
    }
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override
    {
      Debug("strings") << "NotifyClass::eqNotifyTriggerPredicate(" << predicate << ", " << (value ? "true" : "false") << ")" << std::endl;
      if (value) {
        return d_str.propagate(predicate);
      } else {
         return d_str.propagate(predicate.notNode());
      }
    }
    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override
    {
      Debug("strings") << "NotifyClass::eqNotifyTriggerTermMerge(" << tag << ", " << t1 << ", " << t2 << ")" << std::endl;
      if (value) {
      return d_str.propagate(t1.eqNode(t2));
      } else {
      return d_str.propagate(t1.eqNode(t2).notNode());
      }
    }
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override
    {
      Debug("strings") << "NotifyClass::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << ")" << std::endl;
      d_str.conflict(t1, t2);
    }
    void eqNotifyNewClass(TNode t) override
    {
      Debug("strings") << "NotifyClass::eqNotifyNewClass(" << t << std::endl;
      d_str.eqNotifyNewClass(t);
    }
    void eqNotifyPreMerge(TNode t1, TNode t2) override
    {
      Debug("strings") << "NotifyClass::eqNotifyPreMerge(" << t1 << ", " << t2 << std::endl;
      d_str.eqNotifyPreMerge(t1, t2);
    }
    void eqNotifyPostMerge(TNode t1, TNode t2) override
    {
      Debug("strings") << "NotifyClass::eqNotifyPostMerge(" << t1 << ", " << t2 << std::endl;
      d_str.eqNotifyPostMerge(t1, t2);
    }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override
    {
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
  Node d_neg_one;
  CVC4::Rational RMAXINT;
  unsigned d_card_size;
  // Helper functions
  Node getRepresentative( Node t );
  bool hasTerm( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  bool areCareDisequal( TNode x, TNode y );
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
  NodeIntMap d_nf_pairs;
  std::map< Node, std::vector< Node > > d_nf_pairs_data;
  void addNormalFormPair( Node n1, Node n2 );
  bool isNormalFormPair( Node n1, Node n2 );
  bool isNormalFormPair2( Node n1, Node n2 );
  // preReg cache
  NodeSet d_pregistered_terms_cache;
  NodeSet d_registered_terms_cache;
  NodeSet d_length_lemma_terms_cache;
  NodeSet d_skolem_ne_reg_cache;
  // preprocess cache
  StringsPreprocess d_preproc;
  NodeBoolMap d_preproc_cache;
  // extended functions inferences cache
  NodeSet d_extf_infer_cache;
  NodeSet d_extf_infer_cache_u;
  std::vector< Node > d_empty_vec;
  //
  NodeList d_ee_disequalities;
private:
  NodeSet d_congruent;
  std::map< Node, Node > d_eqc_to_const;
  std::map< Node, Node > d_eqc_to_const_base;
  std::map< Node, Node > d_eqc_to_const_exp;
  Node getConstantEqc( Node eqc );
  
  std::map< Node, Node > d_eqc_to_len_term;
  std::vector< Node > d_strings_eqc;
  Node d_emptyString_r;
  class TermIndex {
  public:
    Node d_data;
    std::map< TNode, TermIndex > d_children;
    Node add( TNode n, unsigned index, TheoryStrings* t, Node er, std::vector< Node >& c );
    void clear(){ d_children.clear(); }
  };
  std::map< Kind, TermIndex > d_term_index;
  //list of non-congruent concat terms in each eqc
  std::map< Node, std::vector< Node > > d_eqc;
  std::map< Node, std::vector< Node > > d_flat_form;
  std::map< Node, std::vector< int > > d_flat_form_index;

  void debugPrintFlatForms( const char * tc );
  void debugPrintNormalForms( const char * tc );
  /////////////////////////////////////////////////////////////////////////////
  // MODEL GENERATION
  /////////////////////////////////////////////////////////////////////////////
 public:
  bool collectModelInfo(TheoryModel* m) override;

  /////////////////////////////////////////////////////////////////////////////
  // NOTIFICATIONS
  /////////////////////////////////////////////////////////////////////////////
 public:
  void presolve() override;
  void shutdown() override {}

  /////////////////////////////////////////////////////////////////////////////
  // MAIN SOLVER
  /////////////////////////////////////////////////////////////////////////////
 private:
  void addSharedTerm(TNode n) override;
  EqualityStatus getEqualityStatus(TNode a, TNode b) override;

 private:
  /** SAT-context-dependent information about an equivalence class */
  class EqcInfo {
  public:
    EqcInfo( context::Context* c );
    ~EqcInfo(){}
    /**
     * If non-null, this is a term x from this eq class such that str.len( x )
     * occurs as a term in this SAT context.
     */
    context::CDO< Node > d_length_term;
    /**
     * If non-null, this is a term x from this eq class such that str.code( x )
     * occurs as a term in this SAT context.
     */
    context::CDO<Node> d_code_term;
    context::CDO< unsigned > d_cardinality_lem_k;
    context::CDO< Node > d_normalized_length;
  };
  /** map from representatives to information necessary for equivalence classes */
  std::map< Node, EqcInfo* > d_eqc_info;
  /**
   * Get the above information for equivalence class eqc. If doMake is true,
   * we construct a new information class if one does not exist. The term eqc
   * should currently be a representative of the equality engine of this class.
   */
  EqcInfo * getOrMakeEqcInfo( Node eqc, bool doMake = true );
  //maintain which concat terms have the length lemma instantiated
  NodeNodeMap d_proxy_var;
  NodeNodeMap d_proxy_var_to_length;
  /** All the function terms that the theory has seen */
  context::CDList<TNode> d_functionsTerms;
private:
  //any non-reduced extended functions exist
  context::CDO< bool > d_has_extf;
  /** have we asserted any str.code terms? */
  bool d_has_str_code;
  // static information about extf
  class ExtfInfo {
  public:
    //all variables in this term
    std::vector< Node > d_vars;
  };
  // non-static information about extf
  class ExtfInfoTmp {
  public:
    void init(){
      d_pol = 0;
      d_model_active = true;
    }
    // list of terms that something (does not) contain and their explanation
    std::map< bool, std::vector< Node > > d_ctn;
    std::map< bool, std::vector< Node > > d_ctn_from;
    //polarity
    int d_pol;
    //explanation
    std::vector< Node > d_exp;
    //false if it is reduced in the model
    bool d_model_active;
  };
  std::map< Node, ExtfInfoTmp > d_extf_info_tmp;
private:
  class InferInfo {
  public:
    unsigned d_i;
    unsigned d_j;
    bool d_rev;
    std::vector< Node > d_ant;
    std::vector< Node > d_antn;
    std::map< int, std::vector< Node > > d_new_skolem;
    Node d_conc;
    Inference d_id;
    std::map< Node, bool > d_pending_phase;
    unsigned d_index;
    Node d_nf_pair[2];
    bool sendAsLemma();
  };
  void checkConstantEquivalenceClasses( TermIndex* ti, std::vector< Node >& vecc );
  void checkExtfInference( Node n, Node nr, ExtfInfoTmp& in, int effort );
  Node getSymbolicDefinition( Node n, std::vector< Node >& exp );

  //--------------------------for checkFlatForm
  /**
   * This checks whether there are flat form inferences between eqc[start] and
   * eqc[j] for some j>start. If the flag isRev is true, we check for flat form
   * interferences in the reverse direction of the flat forms. For more details,
   * see checkFlatForms below.
   */
  void checkFlatForm(std::vector<Node>& eqc, unsigned start, bool isRev);
  //--------------------------end for checkFlatForm

  //--------------------------for checkCycles
  Node checkCycles( Node eqc, std::vector< Node >& curr, std::vector< Node >& exp );
  //--------------------------end for checkCycles

  //--------------------------for checkNormalFormsEq
  void normalizeEquivalenceClass( Node n );
  void getNormalForms( Node &eqc, std::vector< std::vector< Node > > &normal_forms, std::vector< Node > &normal_form_src,
                       std::vector< std::vector< Node > > &normal_forms_exp, std::vector< std::map< Node, std::map< bool, int > > >& normal_forms_exp_depend );
  bool detectLoop( std::vector< std::vector< Node > > &normal_forms, int i, int j, int index, int &loop_in_i, int &loop_in_j, unsigned rproc );
  bool processLoop( std::vector< std::vector< Node > > &normal_forms, std::vector< Node > &normal_form_src,
                    int i, int j, int loop_n_index, int other_n_index,int loop_index, int index, InferInfo& info );
  void processNEqc( std::vector< std::vector< Node > > &normal_forms, std::vector< Node > &normal_form_src,
                    std::vector< std::vector< Node > > &normal_forms_exp, std::vector< std::map< Node, std::map< bool, int > > >& normal_forms_exp_depend );
  void processReverseNEq( std::vector< std::vector< Node > > &normal_forms, std::vector< Node > &normal_form_src, 
                          std::vector< std::vector< Node > > &normal_forms_exp, std::vector< std::map< Node, std::map< bool, int > > >& normal_forms_exp_depend, 
                          unsigned i, unsigned j, unsigned& index, unsigned rproc, std::vector< InferInfo >& pinfer );
  void processSimpleNEq( std::vector< std::vector< Node > > &normal_forms, std::vector< Node > &normal_form_src, 
                         std::vector< std::vector< Node > > &normal_forms_exp, std::vector< std::map< Node, std::map< bool, int > > >& normal_forms_exp_depend, 
                         unsigned i, unsigned j, unsigned& index, bool isRev, unsigned rproc, std::vector< InferInfo >& pinfer );
  //--------------------------end for checkNormalFormsEq

  //--------------------------for checkNormalFormsDeq
  void processDeq( Node n1, Node n2 );
  int processReverseDeq( std::vector< Node >& nfi, std::vector< Node >& nfj, Node ni, Node nj );
  int processSimpleDeq( std::vector< Node >& nfi, std::vector< Node >& nfj, Node ni, Node nj, unsigned& index, bool isRev );
  void getExplanationVectorForPrefix( std::vector< std::vector< Node > > &normal_forms_exp, std::vector< std::map< Node, std::map< bool, int > > >& normal_forms_exp_depend,
                                      unsigned i, int index, bool isRev, std::vector< Node >& curr_exp );
  void getExplanationVectorForPrefixEq( std::vector< std::vector< Node > > &normal_forms, std::vector< Node > &normal_form_src,
                                        std::vector< std::vector< Node > > &normal_forms_exp, std::vector< std::map< Node, std::map< bool, int > > >& normal_forms_exp_depend,
                                        unsigned i, unsigned j, int index_i, int index_j, bool isRev, std::vector< Node >& curr_exp );
  //--------------------------end for checkNormalFormsDeq

  //--------------------------------for checkMemberships
  // check membership constraints
  Node mkRegExpAntec(Node atom, Node ant);
  bool checkPDerivative( Node x, Node r, Node atom, bool &addedLemma, std::vector< Node > &nf_exp);
  //check contains
  void checkPosContains( std::vector< Node >& posContains );
  void checkNegContains( std::vector< Node >& negContains );
  //--------------------------------end for checkMemberships

 private:
  void addCarePairs( quantifiers::TermArgTrie * t1, quantifiers::TermArgTrie * t2, unsigned arity, unsigned depth );

 public:
  /** preregister term */
  void preRegisterTerm(TNode n) override;
  /** Expand definition */
  Node expandDefinition(LogicRequest& logicRequest, Node n) override;
  /** Check at effort e */
  void check(Effort e) override;
  /** needs check last effort */
  bool needsCheckLastEffort() override;
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
  StringsPreprocess* getPreprocess() { return &d_preproc; }

 protected:
  /** compute care graph */
  void computeCareGraph() override;

  // do pending merges
  void assertPendingFact(Node atom, bool polarity, Node exp);
  void doPendingFacts();
  void doPendingLemmas();
  bool hasProcessed();
  void addToExplanation(Node a, Node b, std::vector<Node>& exp);
  void addToExplanation(Node lit, std::vector<Node>& exp);

  /** Register term
   *
   * This performs SAT-context-independent registration for a term n, which
   * may cause lemmas to be sent on the output channel that involve
   * "initial refinement lemmas" for n. This includes introducing proxy
   * variables for string terms and asserting that str.code terms are within
   * proper bounds.
   *
   * Effort is one of the following (TODO make enum #1881):
   * 0 : upon preregistration or internal assertion
   * 1 : upon occurrence in length term
   * 2 : before normal form computation
   * 3 : called on normal form terms
   *
   * Based on the strategy, we may choose to add these initial refinement
   * lemmas at one of the following efforts, where if it is not the given
   * effort, the call to this method does nothing.
   */
  void registerTerm(Node n, int effort);
  // send lemma
  void sendInference(std::vector<Node>& exp,
                     std::vector<Node>& exp_n,
                     Node eq,
                     const char* c,
                     bool asLemma = false);
  void sendInference(std::vector<Node>& exp,
                     Node eq,
                     const char* c,
                     bool asLemma = false);
  void sendLemma(Node ant, Node conc, const char* c);
  void sendInfer(Node eq_exp, Node eq, const char* c);
  bool sendSplit(Node a, Node b, const char* c, bool preq = true);
  /** send length lemma
   *
   * This method is called on non-constant string terms n. It sends a lemma
   * on the output channel that ensures that len( n ) >= 0. In particular, the
   * this lemma is typically of the form:
   *   ( n = "" ^ len( n ) = 0 ) OR len( n ) > 0
   * This method also ensures that, when applicable, the left branch is taken
   * first via calls to requirePhase.
   */
  void sendLengthLemma(Node n);
  /** mkConcat **/
  inline Node mkConcat(Node n1, Node n2);
  inline Node mkConcat(Node n1, Node n2, Node n3);
  inline Node mkConcat(const std::vector<Node>& c);
  inline Node mkLength(Node n);
  // mkSkolem
  enum
  {
    sk_id_c_spt,
    sk_id_vc_spt,
    sk_id_vc_bin_spt,
    sk_id_v_spt,
    sk_id_c_spt_rev,
    sk_id_vc_spt_rev,
    sk_id_vc_bin_spt_rev,
    sk_id_v_spt_rev,
    sk_id_ctn_pre,
    sk_id_ctn_post,
    sk_id_dc_spt,
    sk_id_dc_spt_rem,
    sk_id_deq_x,
    sk_id_deq_y,
    sk_id_deq_z,
  };
  std::map<Node, std::map<Node, std::map<int, Node> > > d_skolem_cache;
  /** the set of all skolems we have generated */
  std::unordered_set<Node, NodeHashFunction> d_all_skolems;
  Node mkSkolemCached(
      Node a, Node b, int id, const char* c, int isLenSplit = 0);
  inline Node mkSkolemS(const char* c, int isLenSplit = 0);
  void registerNonEmptySkolem(Node sk);
  // inline Node mkSkolemI(const char * c);
  /** mkExplain **/
  Node mkExplain(std::vector<Node>& a);
  Node mkExplain(std::vector<Node>& a, std::vector<Node>& an);
  /** mkAnd **/
  Node mkAnd(std::vector<Node>& a);
  /** get concat vector */
  void getConcatVec(Node n, std::vector<Node>& c);

  // get equivalence classes
  void getEquivalenceClasses(std::vector<Node>& eqcs);

  // separate into collections with equal length
  void separateByLength(std::vector<Node>& n,
                        std::vector<std::vector<Node> >& col,
                        std::vector<Node>& lts);
  void printConcat(std::vector<Node>& n, const char* c);

  void inferSubstitutionProxyVars(Node n,
                                  std::vector<Node>& vars,
                                  std::vector<Node>& subs,
                                  std::vector<Node>& unproc);

  // Symbolic Regular Expression
 private:
  // regular expression memberships
  NodeList d_regexp_memberships;
  NodeSet d_regexp_ucached;
  NodeSet d_regexp_ccached;
  // stored assertions
  NodeIntMap d_pos_memberships;
  std::map< Node, std::vector< Node > > d_pos_memberships_data;
  NodeIntMap d_neg_memberships;
  std::map< Node, std::vector< Node > > d_neg_memberships_data;
  unsigned getNumMemberships( Node n, bool isPos );
  Node getMembership( Node n, bool isPos, unsigned i );
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
  Node getNextDecisionRequest(unsigned& priority) override;
  // ppRewrite
  Node ppRewrite(TNode atom) override;

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

 private:
  //-----------------------inference steps
  /** check initial
   *
   * This function initializes term indices for each strings function symbol.
   * One key aspect of this construction is that concat terms are indexed by
   * their list of non-empty components. For example, if x = "" is an equality
   * asserted in this SAT context, then y ++ x ++ z may be indexed by (y,z).
   * This method may infer various facts while building these term indices, for
   * instance, based on congruence. An example would be inferring:
   *   y ++ x ++ z = y ++ z
   * if both terms are registered in this SAT context.
   *
   * This function should be called as a first step of any strategy.
   */
  void checkInit();
  /** check constant equivalence classes
   *
   * This function infers whether CONCAT terms can be simplified to constants.
   * For example, if x = "a" and y = "b" are equalities in the current SAT
   * context, then we may infer x ++ "c" ++ y is equivalent to "acb". In this
   * case, we infer the fact x ++ "c" ++ y = "acb".
   */
  void checkConstantEquivalenceClasses();
  /** check extended functions evaluation
   *
   * This applies "context-dependent simplification" for all active extended
   * function terms in this SAT context. This infers facts of the form:
   *   x = c => f( t1 ... tn ) = c'
   * where the rewritten form of f( t1...tn ) { x |-> c } is c', and x = c
   * is a (tuple of) equalities that are asserted in this SAT context, and
   * f( t1 ... tn ) is a term from this SAT context.
   *
   * For more details, this is steps 4 when effort=0 and step 6 when
   * effort=1 from Strategy 1 in Reynolds et al, "Scaling up DPLL(T) String
   * Solvers using Context-Dependent Simplification", CAV 2017. When called with
   * effort=3, we apply context-dependent simplification based on model values.
   */
  void checkExtfEval(int effort);
  /** check cycles
   *
   * This inference schema ensures that a containment ordering < over the
   * string equivalence classes is acyclic. We define this ordering < such that
   * for equivalence classes e1 = { t1...tn } and e2 = { s1...sm }, e1 < e2
   * if there exists a ti whose flat form (see below) is [w1...sj...wk] for
   * some i,j. If e1 < ... < en < e1 for some chain, we infer that the flat
   * form components that do not constitute this chain, e.g. (w1...wk) \ sj
   * in the flat form above, must be empty.
   *
   * For more details, see the inference S-Cycle in Liang et al CAV 2014.
   */
  void checkCycles();
  /** check flat forms
   *
   * This applies an inference schema based on "flat forms". The flat form of a
   * string term t is a vector of representative terms [r1, ..., rn] such that
   * t is of the form t1 ++ ... ++ tm and r1 ++ ... ++ rn is equivalent to
   * rewrite( [t1] ++ ... ++ [tm] ), where [t1] denotes the representative of
   * the equivalence class containing t1. For example, if t is y ++ z ++ z,
   * E is { y = "", w = z }, and w is the representative of the equivalence
   * class { w, z }, then the flat form of t is [w, w]. Say t1 and t2 are terms
   * in the same equivalence classes with flat forms [r1...rn] and [s1...sm].
   * We may infer various facts based on this pair of terms. For example:
   *   ri = si, if ri != si, rj == sj for each j < i, and len(ri)=len(si),
   *   rn = sn, if n=m and rj == sj for each j < n,
   *   ri = empty, if n=m+1 and ri == rj for each i=1,...,m.
   * We refer to these as "unify", "endpoint-eq" and "endpoint-emp" inferences
   * respectively.
   *
   * Notice that this inference scheme is an optimization and not needed for
   * model-soundness. The motivation for this schema is that it is simpler than
   * checkNormalFormsEq, which can be seen as a recursive version of this
   * schema (see difference of "normal form" vs "flat form" below), and
   * checkNormalFormsEq is complete, in the sense that if it passes with no
   * inferences, we are ensured that all string equalities in the current
   * context are satisfied.
   *
   * Must call checkCycles before this function in a strategy.
   */
  void checkFlatForms();
  /** check normal forms equalities
   *
   * This applies an inference schema based on "normal forms". The normal form
   * of an equivalence class of string terms e = {t1, ..., tn} union {x1....xn},
   * where t1...tn are concatenation terms is a vector of representative terms
   * [r1, ..., rm] such that:
   * (1) if n=0, then m=1 and r1 is the representative of e,
   * (2) if n>0, say
   *   t1 = t^1_1 ++ ... ++ t^1_m_1
   *   ...
   *   tn = t^1_n ++ ... ++ t^_m_n
   * for *each* i=1, ..., n, the result of concenating the normal forms of
   * t^1_1 ++ ... ++ t^1_m_1 is equal to [r1, ..., rm]. If an equivalence class
   * can be assigned a normal form, then all equalities between ti and tj are
   * satisfied by all models that correspond to extensions of the current
   * assignment. For further detail on this terminology, see Liang et al
   * CAV 2014.
   *
   * Notice that all constant words are implicitly considered concatentation
   * of their characters, e.g. "abc" is treated as "a" ++ "b" ++ "c".
   *
   * At a high level, we build normal forms for equivalence classes bottom-up,
   * starting with equivalence classes that are minimal with respect to the
   * containment ordering < computed during checkCycles. While computing a
   * normal form for an equivalence class, we may infer equalities between
   * components of strings that must be equal (e.g. x=y when x++z == y++w when
   * len(x)==len(y) is asserted), derive conflicts if two strings have disequal
   * prefixes/suffixes (e.g. "a" ++ x == "b" ++ y is a conflict), or split
   * string terms into smaller components using fresh skolem variables (see
   * Inference values with names "SPLIT"). We also may introduce regular
   * expression constraints in this method for looping word equations (see
   * the Inference INFER_FLOOP).
   *
   * If this inference schema returns no facts, lemmas, or conflicts, then
   * we have successfully assigned normal forms for all equivalence classes, as
   * stored in d_normal_forms. Otherwise, this method may add a fact, lemma, or
   * conflict based on inferences in the Inference enumeration above.
   */
  void checkNormalFormsEq();
  /** check normal forms disequalities
   *
   * This inference schema can be seen as the converse of the above schema. In
   * particular, it ensures that each pair of distinct equivalence classes
   * e1 and e2 have distinct normal forms.
   *
   * This method considers all pairs of distinct equivalence classes (e1,e2)
   * such that len(x1)==len(x2) is asserted for some x1 in e1 and x2 in e2. It
   * then traverses the normal forms of x1 and x2, say they are [r1, ..., rn]
   * and [s1, ..., sm]. For the minimial i such that ri!=si, if ri and si are
   * disequal and have the same length, then x1 and x2 have distinct normal
   * forms. Otherwise, we may add splitting lemmas on the length of ri and si,
   * or split on an equality between ri and si.
   *
   * If this inference schema returns no facts, lemmas, or conflicts, then all
   * disequalities between string terms are satisfied by all models that are
   * extensions of the current assignment.
   */
  void checkNormalFormsDeq();
  /** check codes
   *
   * This inference schema ensures that constraints between str.code terms
   * are satisfied by models that correspond to extensions of the current
   * assignment. In particular, this method ensures that str.code can be
   * given an interpretation that is injective for string arguments with length
   * one. It may add lemmas of the form:
   *   str.code(x) == -1 V str.code(x) != str.code(y) V x == y
   */
  void checkCodes();
  /** check lengths for equivalence classes
   *
   * This inference schema adds lemmas of the form:
   *   E => len( x ) = rewrite( len( r1 ++ ... ++ rn ) )
   * where [r1, ..., rn] is the normal form of the equivalence class containing
   * x. This schema is not required for correctness but experimentally has
   * shown to be helpful.
   */
  void checkLengthsEqc();
  /** check extended function reductions
   *
   * This adds "reduction" lemmas for each active extended function in this SAT
   * context. These are generally lemmas of the form:
   *   F[t1...tn,k] ^ f( t1 ... tn ) = k
   * where f( t1 ... tn ) is an active extended function, k is a fresh constant
   * and F is a formula that constrains k based on the definition of f.
   *
   * For more details, this is step 7 from Strategy 1 in Reynolds et al,
   * CAV 2017. We stratify this in practice, where calling this with effort=1
   * reduces some of the "easier" extended functions, and effort=2 reduces
   * the rest.
   */
  void checkExtfReductions(int effort);
  /** check regular expression memberships
   *
   * This checks the satisfiability of all regular expression memberships
   * of the form (not) s in R. We use various heuristic techniques based on
   * unrolling, combined with techniques from Liang et al, "A Decision Procedure
   * for Regular Membership and Length Constraints over Unbounded Strings",
   * FroCoS 2015.
   */
  void checkMemberships();
  /** check cardinality
   *
   * This function checks whether a cardinality inference needs to be applied
   * to a set of equivalence classes. For details, see Step 5 of the proof
   * procedure from Liang et al, CAV 2014.
   */
  void checkCardinality();
  //-----------------------end inference steps

  //-----------------------representation of the strategy
  /** is strategy initialized */
  bool d_strategy_init;
  /** run the given inference step */
  void runInferStep(InferStep s, int effort);
  /** the strategy */
  std::vector<InferStep> d_infer_steps;
  /** the effort levels */
  std::vector<int> d_infer_step_effort;
  /** the range (begin, end) of steps to run at given efforts */
  std::map<Effort, std::pair<unsigned, unsigned> > d_strat_steps;
  /** do we have a strategy for effort e? */
  bool hasStrategyEffort(Effort e) const;
  /** initialize the strategy
   *
   * This adds (s,effort) as a strategy step to the vectors d_infer_steps and
   * d_infer_step_effort. This indicates that a call to runInferStep should
   * be run as the next step in the strategy. If addBreak is true, we add
   * a BREAK to the strategy following this step.
   */
  void addStrategyStep(InferStep s, int effort = 0, bool addBreak = true);
  /** initialize the strategy
   *
   * This initializes the above information based on the options. This makes
   * a series of calls to addStrategyStep above.
   */
  void initializeStrategy();
  /** run strategy
   *
   * This executes the inference steps starting at index sbegin and ending at
   * index send. We exit if any step in this sequence adds a lemma or infers a
   * fact.
   */
  void runStrategy(unsigned sbegin, unsigned send);
  //-----------------------end representation of the strategy

};/* class TheoryStrings */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__THEORY_STRINGS_H */
