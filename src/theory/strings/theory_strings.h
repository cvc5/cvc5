/*********************                                                        */
/*! \file theory_strings.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory of strings
 **
 ** Theory of strings.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__THEORY_STRINGS_H
#define CVC4__THEORY__STRINGS__THEORY_STRINGS_H

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "expr/attribute.h"
#include "expr/node_trie.h"
#include "theory/decision_manager.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/normal_form.h"
#include "theory/strings/regexp_elim.h"
#include "theory/strings/regexp_operation.h"
#include "theory/strings/regexp_solver.h"
#include "theory/strings/skolem_cache.h"
#include "theory/strings/theory_strings_preprocess.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

#include <climits>
#include <deque>

namespace CVC4 {
namespace theory {
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
  friend class InferenceManager;
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
  //--------------------------for checkExtfReductions
  /** do reduction
   *
   * This is called when an extended function application n is not able to be
   * simplified by context-depdendent simplification, and we are resorting to
   * expanding n to its full semantics via a reduction. This method returns
   * true if it successfully reduced n by some reduction and sets isCd to
   * true if the reduction was (SAT)-context-dependent, and false otherwise.
   * The argument effort has the same meaning as in checkExtfReductions.
   */
  bool doReduction(int effort, Node n, bool& isCd);
  //--------------------------end for checkExtfReductions

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

  //--------------------------- equality engine
  /**
   * Get the representative of t in the equality engine of this class, or t
   * itself if it is not registered as a term.
   */
  Node getRepresentative(Node t);
  /** Is t registered as a term in the equality engine of this class? */
  bool hasTerm(Node a);
  /**
   * Are a and b equal according to the equality engine of this class? Also
   * returns true if a and b are identical.
   */
  bool areEqual(Node a, Node b);
  /**
   * Are a and b disequal according to the equality engine of this class? Also
   * returns true if the representative of a and b are distinct constants.
   */
  bool areDisequal(Node a, Node b);
  //--------------------------- end equality engine

  //--------------------------- helper functions
  /** get length with explanation
   *
   * If possible, this returns an arithmetic term that exists in the current
   * context that is equal to the length of te, or otherwise returns the
   * length of t. It adds to exp literals that hold in the current context that
   * explain why that term is equal to the length of t. For example, if
   * we have assertions:
   *   len( x ) = 5 ^ z = x ^ x = y,
   * then getLengthExp( z, exp, y ) returns len( x ) and adds { z = x } to
   * exp. On the other hand, getLengthExp( z, exp, x ) returns len( x ) and
   * adds nothing to exp.
   */
  Node getLengthExp(Node t, std::vector<Node>& exp, Node te);
  /** shorthand for getLengthExp(t, exp, t) */
  Node getLength(Node t, std::vector<Node>& exp);
  /** get normal string
   *
   * This method returns the node that is equivalent to the normal form of x,
   * and adds the corresponding explanation to nf_exp.
   *
   * For example, if x = y ++ z is an assertion in the current context, then
   * this method returns the term y ++ z and adds x = y ++ z to nf_exp.
   */
  Node getNormalString(Node x, std::vector<Node>& nf_exp);
  //-------------------------- end helper functions

 private:
  // Constants
  Node d_emptyString;
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  /** the cardinality of the alphabet */
  unsigned d_card_size;
  /** The notify class */
  NotifyClass d_notify;
  /** Equaltity engine */
  eq::EqualityEngine d_equalityEngine;
  /** The (custom) output channel of the theory of strings */
  InferenceManager d_im;
  /** Are we in conflict */
  context::CDO<bool> d_conflict;
  /** map from terms to their normal forms */
  std::map<Node, NormalForm> d_normal_form;
  /** get normal form */
  NormalForm& getNormalForm(Node n);
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
  /** preprocessing utility, for performing strings reductions */
  StringsPreprocess d_preproc;
  // extended functions inferences cache
  NodeSet d_extf_infer_cache;
  NodeSet d_extf_infer_cache_u;
  std::vector< Node > d_empty_vec;
  //
  NodeList d_ee_disequalities;
private:
  NodeSet d_congruent;
  /**
   * The following three vectors are used for tracking constants that each
   * equivalence class is entailed to be equal to.
   * - The map d_eqc_to_const maps (representatives) r of equivalence classes to
   * the constant that that equivalence class is entailed to be equal to,
   * - The term d_eqc_to_const_base[r] is the term in the equivalence class r
   * that is entailed to be equal to the constant d_eqc_to_const[r],
   * - The term d_eqc_to_const_exp[r] is the explanation of why
   * d_eqc_to_const_base[r] is equal to d_eqc_to_const[r].
   *
   * For example, consider the equivalence class { r, x++"a"++y, x++z }, and
   * assume x = "" and y = "bb" in the current context. We have that
   *   d_eqc_to_const[r] = "abb",
   *   d_eqc_to_const_base[r] = x++"a"++y
   *   d_eqc_to_const_exp[r] = ( x = "" AND y = "bb" )
   *
   * This information is computed during checkInit and is used during various
   * inference schemas for deriving inferences.
   */
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
  /**
   * Map string terms to their "proxy variables". Proxy variables are used are
   * intermediate variables so that length information can be communicated for
   * constants. For example, to communicate that "ABC" has length 3, we
   * introduce a proxy variable v_{"ABC"} for "ABC", and assert:
   *   v_{"ABC"} = "ABC" ^ len( v_{"ABC"} ) = 3
   * Notice this is required since we cannot directly write len( "ABC" ) = 3,
   * which rewrites to 3 = 3.
   * In the above example, we store "ABC" -> v_{"ABC"} in this map.
   */
  NodeNodeMap d_proxy_var;
  /**
   * Map from proxy variables to their normalized length. In the above example,
   * we store "ABC" -> 3.
   */
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

 private:
  /** Length status, used for the registerLength function below */
  enum LengthStatus
  {
    LENGTH_SPLIT,
    LENGTH_ONE,
    LENGTH_GEQ_ONE
  };

  /** register length
   *
   * This method is called on non-constant string terms n. It sends a lemma
   * on the output channel that ensures that the length n satisfies its assigned
   * status (given by argument s).
   *
   * If the status is LENGTH_ONE, we send the lemma len( n ) = 1.
   *
   * If the status is LENGTH_GEQ, we send a lemma n != "" ^ len( n ) > 0.
   *
   * If the status is LENGTH_SPLIT, we send a send a lemma of the form:
   *   ( n = "" ^ len( n ) = 0 ) OR len( n ) > 0
   * This method also ensures that, when applicable, the left branch is taken
   * first via calls to requirePhase.
   */
  void registerLength(Node n, LengthStatus s);

  //------------------------- candidate inferences
  class InferInfo
  {
   public:
    /** for debugging
     *
     * The base pair of strings d_i/d_j that led to the inference, and whether
     * (d_rev) we were processing the normal forms of these strings in reverse
     * direction.
     */
    Node d_i;
    Node d_j;
    bool d_rev;
    std::vector<Node> d_ant;
    std::vector<Node> d_antn;
    std::map<LengthStatus, std::vector<Node> > d_new_skolem;
    Node d_conc;
    Inference d_id;
    std::map<Node, bool> d_pending_phase;
    unsigned d_index;
    Node d_nf_pair[2];
    bool sendAsLemma();
  };
  //------------------------- end candidate inferences
  /** cache of all skolems */
  SkolemCache d_sk_cache;

  void checkConstantEquivalenceClasses( TermIndex* ti, std::vector< Node >& vecc );
  /** Get proxy variable
   *
   * If this method returns the proxy variable for (string) term n if one
   * exists, otherwise it returns null.
   */
  Node getProxyVariableFor(Node n) const;
  /** Get symbolic definition
   *
   * This method returns the "symbolic definition" of n, call it n', and
   * populates the vector exp with an explanation such that exp => n = n'.
   *
   * The symbolic definition of n is the term where (maximal) subterms of n
   * are replaced by their proxy variables. For example, if we introduced
   * proxy variable v for x ++ y, then given input x ++ y = w, this method
   * returns v = w and adds v = x ++ y to exp.
   */
  Node getSymbolicDefinition(Node n, std::vector<Node>& exp) const;

  //--------------------------for checkExtfEval
  /**
   * Non-static information about an extended function t. This information is
   * constructed and used during the check extended function evaluation
   * inference schema.
   *
   * In the following, we refer to the "context-dependent simplified form"
   * of a term t to be the result of rewriting t * sigma, where sigma is a
   * derivable substitution in the current context. For example, the
   * context-depdendent simplified form of contains( x++y, "a" ) given
   * sigma = { x -> "" } is contains(y,"a").
   */
  class ExtfInfoTmp
  {
   public:
    ExtfInfoTmp() : d_model_active(true) {}
    /**
     * If s is in d_ctn[true] (resp. d_ctn[false]), then contains( t, s )
     * (resp. ~contains( t, s )) holds in the current context. The vector
     * d_ctn_from is the explanation for why this holds. For example,
     * if d_ctn[false][i] is "A", then d_ctn_from[false][i] might be
     * t = x ++ y AND x = "" AND y = "B".
     */
    std::map<bool, std::vector<Node> > d_ctn;
    std::map<bool, std::vector<Node> > d_ctn_from;
    /**
     * The constant that t is entailed to be equal to, or null if none exist.
     */
    Node d_const;
    /**
     * The explanation for why t is equal to its context-dependent simplified
     * form.
     */
    std::vector<Node> d_exp;
    /** This flag is false if t is reduced in the model. */
    bool d_model_active;
  };
  /** map extended functions to the above information */
  std::map<Node, ExtfInfoTmp> d_extf_info_tmp;
  /** check extended function inferences
   *
   * This function makes additional inferences for n that do not contribute
   * to its reduction, but may help show a refutation.
   *
   * This function is called when the context-depdendent simplified form of
   * n is nr. The argument "in" is the information object for n. The argument
   * "effort" has the same meaning as the effort argument of checkExtfEval.
   */
  void checkExtfInference(Node n, Node nr, ExtfInfoTmp& in, int effort);
  //--------------------------end for checkExtfEval

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
  /** normalize equivalence class
   *
   * This method attempts to build a "normal form" for the equivalence class
   * of string term n (for more details on normal forms, see normal_form.h
   * or see Liang et al CAV 2014). In particular, this method checks whether the
   * current normal form for each term in this equivalence class is identical.
   * If it is not, then we add an inference via sendInference and abort the
   * call.
   */
  void normalizeEquivalenceClass( Node n );
  /**
   * For each term in the equivalence class of eqc, this adds data regarding its
   * normal form to normal_forms. The map term_to_nf_index maps terms to the
   * index in normal_forms where their normal form data is located.
   */
  void getNormalForms(Node eqc,
                      std::vector<NormalForm>& normal_forms,
                      std::map<Node, unsigned>& term_to_nf_index);
  /** process normalize equivalence class
   *
   * This is called when an equivalence class contains a set of terms that
   * have normal forms given by the argument normal_forms. It either
   * verifies that all normal forms in this vector are identical, or otherwise
   * adds a conflict, lemma, or inference via the sendInference method.
   *
   * To prioritize one inference versus another, it builds a set of possible
   * inferences, at most two for each pair of distinct normal forms,
   * corresponding to processing the normal form pair in the (forward, reverse)
   * directions. Once all possible inferences are recorded, it executes the
   * one with highest priority based on the enumeration type Inference.
   */
  void processNEqc(std::vector<NormalForm>& normal_forms);
  /** process simple normal equality
   *
   * This method is called when two equal terms have normal forms nfi and nfj.
   * It adds (typically at most one) possible inference to the vector pinfer.
   * This inference is in the form of an InferInfo object, which stores the
   * necessary information regarding how to process the inference.
   *
   * index: The index in the normal form vectors (nfi.d_nf and nfj.d_nf) that
   *   we are currently checking. This method will increment this index until
   *   it finds an index where these vectors differ, or until it reaches the
   *   end of these vectors.
   * isRev: Whether we are processing the normal forms in reverse direction.
   *   Notice in this case the normal form vectors have been reversed, hence,
   *   many operations are identical to the forward case, e.g. index is
   *   incremented not decremented, while others require special care, e.g.
   *   constant strings "ABC" in the normal form vectors are not reversed to
   *   "CBA" and hence all operations should assume a flipped semantics for
   *   constants when isRev is true,
   * rproc: the number of string components on the suffix of the normal form of
   *   nfi and nfj that were already processed. This is used when using
   *   fowards/backwards traversals of normal forms to ensure that duplicate
   *   inferences are not processed.
   * pinfer: the set of possible inferences we add to.
   */
  void processSimpleNEq(NormalForm& nfi,
                        NormalForm& nfj,
                        unsigned& index,
                        bool isRev,
                        unsigned rproc,
                        std::vector<InferInfo>& pinfer);
  //--------------------------end for checkNormalFormsEq

  //--------------------------for checkNormalFormsEq with loops
  bool detectLoop(NormalForm& nfi,
                  NormalForm& nfj,
                  int index,
                  int& loop_in_i,
                  int& loop_in_j,
                  unsigned rproc);

  /**
   * Result of processLoop() below.
   */
  enum class ProcessLoopResult
  {
    /** Loop processing made an inference */
    INFERENCE,
    /** Loop processing detected a conflict */
    CONFLICT,
    /** Loop not processed or no loop detected */
    SKIPPED,
  };

  ProcessLoopResult processLoop(NormalForm& nfi,
                                NormalForm& nfj,
                                int loop_index,
                                int index,
                                InferInfo& info);
  //--------------------------end for checkNormalFormsEq with loops

  //--------------------------for checkNormalFormsDeq
  void processDeq( Node n1, Node n2 );
  int processReverseDeq( std::vector< Node >& nfi, std::vector< Node >& nfj, Node ni, Node nj );
  int processSimpleDeq( std::vector< Node >& nfi, std::vector< Node >& nfj, Node ni, Node nj, unsigned& index, bool isRev );
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
  void addCarePairs(TNodeTrie* t1,
                    TNodeTrie* t2,
                    unsigned arity,
                    unsigned depth);

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
  /**
   * Are x and y shared terms that are not equal? This is used for constructing
   * the care graph in the above function.
   */
  bool areCareDisequal(TNode x, TNode y);

  /** assert pending fact
   *
   * This asserts atom with polarity to the equality engine of this class,
   * where exp is the explanation of why (~) atom holds.
   *
   * This call may trigger further initialization steps involving the terms
   * of atom, including calls to registerTerm.
   */
  void assertPendingFact(Node atom, bool polarity, Node exp);
  /**
   * Adds equality a = b to the vector exp if a and b are distinct terms. It
   * must be the case that areEqual( a, b ) holds in this context.
   */
  void addToExplanation(Node a, Node b, std::vector<Node>& exp);
  /** Adds lit to the vector exp if it is non-null */
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

  /**
   * Are we in conflict? This returns true if this theory has called its output
   * channel's conflict method in the current SAT context.
   */
  bool inConflict() const { return d_conflict; }

  /** mkConcat **/
  inline Node mkConcat(Node n1, Node n2);
  inline Node mkConcat(Node n1, Node n2, Node n3);
  inline Node mkConcat(const std::vector<Node>& c);
  inline Node mkLength(Node n);

  /** mkExplain **/
  Node mkExplain(std::vector<Node>& a);
  Node mkExplain(std::vector<Node>& a, std::vector<Node>& an);

 protected:

  /** get equivalence classes
   *
   * This adds the representative of all equivalence classes to eqcs
   */
  void getEquivalenceClasses(std::vector<Node>& eqcs);
  /** get relevant equivalence classes
   *
   * This adds the representative of all equivalence classes that contain at
   * least one term in termSet.
   */
  void getRelevantEquivalenceClasses(std::vector<Node>& eqcs,
                                     std::set<Node>& termSet);

  // separate into collections with equal length
  void separateByLength(std::vector<Node>& n,
                        std::vector<std::vector<Node> >& col,
                        std::vector<Node>& lts);
  void printConcat(std::vector<Node>& n, const char* c);

  // Symbolic Regular Expression
 private:
  /** regular expression solver module */
  RegExpSolver d_regexp_solver;
  /** regular expression elimination module */
  RegExpElimination d_regexp_elim;

  // Finite Model Finding
 private:
  NodeSet d_input_vars;
  context::CDO< Node > d_input_var_lsum;
  context::CDHashMap< int, Node > d_cardinality_lits;
  context::CDO< int > d_curr_cardinality;
  /** String sum of lengths decision strategy
   *
   * This decision strategy enforces that len(x_1) + ... + len(x_k) <= n
   * for a minimal natural number n, where x_1, ..., x_n is the list of
   * input variables of the problem of type String.
   *
   * This decision strategy is enabled by option::stringsFmf().
   */
  class StringSumLengthDecisionStrategy : public DecisionStrategyFmf
  {
   public:
    StringSumLengthDecisionStrategy(context::Context* c,
                                    context::UserContext* u,
                                    Valuation valuation);
    /** make literal */
    Node mkLiteral(unsigned i) override;
    /** identify */
    std::string identify() const override;
    /** is initialized */
    bool isInitialized();
    /** initialize */
    void initialize(const std::vector<Node>& vars);

    /*
     * Do not hide the zero-argument version of initialize() inherited from the
     * base class
     */
    using DecisionStrategyFmf::initialize;

   private:
    /**
     * User-context-dependent node corresponding to the sum of the lengths of
     * input variables of type string
     */
    context::CDO<Node> d_input_var_lsum;
  };
  /** an instance of the above class */
  std::unique_ptr<StringSumLengthDecisionStrategy> d_sslds;

 public:
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

#endif /* CVC4__THEORY__STRINGS__THEORY_STRINGS_H */
