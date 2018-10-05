/*********************                                                        */
/*! \file ce_guided_single_inv.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing single invocation synthesis conjectures
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_SINGLE_INV_H
#define __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_SINGLE_INV_H

#include "context/cdlist.h"
#include "theory/quantifiers/sygus/ce_guided_single_inv_sol.h"
#include "theory/quantifiers/inst_match_trie.h"
#include "theory/quantifiers/cegqi/inst_strategy_cegqi.h"
#include "theory/quantifiers/single_inv_partition.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SynthConjecture;
class CegSingleInv;

class CegqiOutputSingleInv : public CegqiOutput {
 public:
 CegqiOutputSingleInv(CegSingleInv* out) : d_out(out) {}
 virtual ~CegqiOutputSingleInv() {}
 CegSingleInv* d_out;
 bool doAddInstantiation(std::vector<Node>& subs) override;
 bool isEligibleForInstantiation(Node n) override;
 bool addLemma(Node lem) override;
};

class DetTrace {
private:
  class DetTraceTrie {
  public:
    std::map< Node, DetTraceTrie > d_children;
    bool add( Node loc, std::vector< Node >& val, unsigned index = 0 );
    void clear() { d_children.clear(); }
    Node constructFormula( std::vector< Node >& vars, unsigned index = 0 );
  };
  DetTraceTrie d_trie;
public:
  std::vector< Node > d_curr;
  bool increment( Node loc, std::vector< Node >& vals );
  Node constructFormula( std::vector< Node >& vars );
  void print( const char* c );
};

/**
 * This class is used for inferring that an arbitrary synthesis conjecture
 * corresponds to an invariant synthesis problem for some predicate (d_func).
 *
 * The invariant-to-synthesize can either be explicitly given, via a call
 * to initialize( f, vars ), or otherwise inferred if this method is not called.
 */
class TransitionInference {
 private:
  /** process disjunct
   *
   * The purpose of this function is to infer pre/post/transition conditions
   * for a (possibly unknown) invariant-to-synthesis, given a conjunct from
   * an arbitrary synthesis conjecture.
   *
   * Assume our negated synthesis conjecture is of the form:
   *    forall f. exists x. (and (or F11 ... F1{m_1}) ... (or Fn1 ... Fn{m_n}))
   * This method is called on each (or Fi1 ... Fi{m_i}), where topLevel is true
   * for each of Fi1...F1{m_i} and false otherwise. It adds each of Fi1..Fi{m_i}
   * to disjuncts.
   *
   * If this method returns true, then (1) all applications of free function
   * symbols have operator d_func. Note this function may set d_func to a
   * function symbol in n if d_func was null prior to this call. In other words,
   * this method may infer the subject of the invariant synthesis problem;
   * (2) all occurrences of d_func are "top-level", that is, each Fij may be
   * of the form (not) <d_func>( tj ), but otherwise d_func does not occur in
   * (or Fi1 ... Fi{m_i}); (3) there exists at most one occurrence of
   * <d_func>( tj ), and (not <d_func>( tk )).
   *
   * If the above conditions are met, then terms[true] is set to <d_func>( tj )
   * if Fij is <d_func>( tj ) for some j, and likewise terms[false]
   * is set to <d_func>( tk ) if Fik is (not <d_func>( tk )) for some k.
   *
   * The argument visited caches the results of this function for (topLevel, n).
   */
  bool processDisjunct(Node n,
                       std::map<bool, Node>& terms,
                       std::vector<Node>& disjuncts,
                       std::map<bool, std::map<Node, bool> >& visited,
                       bool topLevel);
  void getConstantSubstitution( std::vector< Node >& vars, std::vector< Node >& disjuncts, std::vector< Node >& const_var, std::vector< Node >& const_subs, bool reqPol );
  bool d_complete;
  /** get normalized substitution
   *
   * This method takes as input a node curr of the form I( t1, ..., tn ) and
   * a vector of variables pvars, where pvars.size()=n. For each ti that is
   * a variable, it adds ti to vars, and pvars[i] to subs. For each ti that is
   * not a variable, it adds the disequality ti != pvars[i] to disjuncts.
   *
   * This function is used for instance to normalize an arbitrary application of
   * I so that is over arguments pvars. For instance if curr is I(3,5,y) and
   * pvars = { x1,x2,x3 }, then the formula:
   *   I(3,5,y) ^ P(y)
   * is equivalent to:
   *   x1 != 3 V x2 != 5 V I(x1,x2,x3) V P( y ) { y -> x3 }
   * Here, we add y and x3 to vars and subs respectively, and x1!=3 and x2!=5
   * to disjuncts.
   */
  void getNormalizedSubstitution(Node curr,
                                 const std::vector<Node>& pvars,
                                 std::vector<Node>& vars,
                                 std::vector<Node>& subs,
                                 std::vector<Node>& disjuncts);

 public:
  TransitionInference() : d_complete( false ) {}
  std::vector< Node > d_vars;
  std::vector< Node > d_prime_vars;
  /**
   * The function (predicate) that is the subject of the invariant synthesis
   * problem we are inferring.
   */
  Node d_func;
  
  class Component {
  public:
    Component(){}
    Node d_this;
    std::vector< Node > d_conjuncts;
    std::map< Node, std::map< Node, Node > > d_const_eq;
    bool has( Node c ) { return std::find( d_conjuncts.begin(), d_conjuncts.end(), c )!=d_conjuncts.end(); }
  };
  std::map< int, Component > d_com;
  
  void initialize( Node f, std::vector< Node >& vars );
  void process( Node n );
  Node getComponent( int i );
  bool isComplete() { return d_complete; }
  
  // 0 : success, 1 : terminated, 2 : counterexample, -1 : invalid
  int initializeTrace( DetTrace& dt, Node loc, bool fwd = true );
  int incrementTrace( DetTrace& dt, Node loc, bool fwd = true );
  int initializeTrace( DetTrace& dt, bool fwd = true );
  int incrementTrace( DetTrace& dt, bool fwd = true );
  Node constructFormulaTrace( DetTrace& dt );
};

// this class infers whether a conjecture is single invocation (Reynolds et al CAV 2015), and sets up the
// counterexample-guided quantifier instantiation utility (d_cinst), and methods for solution
// reconstruction (d_sol).
// It also has more advanced techniques for:
// (1) partitioning a conjecture into single invocation / non-single invocation portions for invariant synthesis,
// (2) inferring whether the conjecture corresponds to a deterministic transistion system (by utility d_ti).
// For these techniques, we may generate a template (d_templ) which specifies a restricted
// solution space. We may in turn embed this template as a SyGuS grammar.
class CegSingleInv
{
 private:
  friend class CegqiOutputSingleInv;
  //presolve
  void collectPresolveEqTerms( Node n,
                               std::map< Node, std::vector< Node > >& teq );
  void getPresolveEqConjuncts( std::vector< Node >& vars,
                               std::vector< Node >& terms,
                               std::map< Node, std::vector< Node > >& teq,
                               Node n, std::vector< Node >& conj );
  // constructing solution
  Node constructSolution(std::vector<unsigned>& indices, unsigned i,
                         unsigned index, std::map<Node, Node>& weak_imp);
  Node postProcessSolution(Node n);
 private:
  /** pointer to the quantifiers engine */
  QuantifiersEngine* d_qe;
  /** the parent of this class */
  SynthConjecture* d_parent;
  // single invocation inference utility
  SingleInvocationPartition* d_sip;
  // transition inference module for each function to synthesize
  std::map< Node, TransitionInference > d_ti;
  // solution reconstruction
  CegSingleInvSol* d_sol;
  // the instantiator's output channel
  CegqiOutputSingleInv* d_cosi;
  // the instantiator
  std::unique_ptr<CegInstantiator> d_cinst;

  // list of skolems for each argument of programs
  std::vector<Node> d_single_inv_arg_sk;
  // list of variables/skolems for each program
  std::vector<Node> d_single_inv_var;
  std::vector<Node> d_single_inv_sk;
  std::map<Node, int> d_single_inv_sk_index;
  // program to solution index
  std::map<Node, unsigned> d_prog_to_sol_index;
  // lemmas produced
  inst::InstMatchTrie d_inst_match_trie;
  inst::CDInstMatchTrie* d_c_inst_match_trie;
  // original conjecture
  Node d_orig_conjecture;
  // solution
  Node d_orig_solution;
  Node d_solution;
  Node d_sygus_solution;
 public:
  // lemmas produced
  std::vector<Node> d_lemmas_produced;
  std::vector<std::vector<Node> > d_inst;

 private:
  std::vector<Node> d_curr_lemmas;
  // add instantiation
  bool doAddInstantiation( std::vector< Node >& subs );
  //is eligible for instantiation
  bool isEligibleForInstantiation( Node n );
  // add lemma
  bool addLemma( Node lem );
  // conjecture
  Node d_quant;
  Node d_simp_quant;
  // are we single invocation?
  bool d_single_invocation;
  // single invocation portion of quantified formula
  Node d_single_inv;
  // transition relation version per program
  std::map< Node, Node > d_trans_pre;
  std::map< Node, Node > d_trans_post;
  // the template for each function to synthesize
  std::map< Node, Node > d_templ;
  // the template argument for each function to synthesize (occurs in exactly one position of its template)
  std::map< Node, Node > d_templ_arg;
  
 public:
  CegSingleInv(QuantifiersEngine* qe, SynthConjecture* p);
  ~CegSingleInv();

  // get simplified conjecture
  Node getSimplifiedConjecture() { return d_simp_quant; }
 public:
  /** get the single invocation lemma(s)
   *
   * This adds lemmas to lem that initializes this class for doing
   * counterexample-guided instantiation for the synthesis conjecture. These
   * lemmas correspond to the negation of the body of the (anti-skolemized)
   * form of the conjecture for fresh skolems.
   *
   * Argument g is guard, for which all the above lemmas are guarded.
   */
  void getInitialSingleInvLemma(Node g, std::vector<Node>& lems);
  // initialize this class for synthesis conjecture q
  void initialize( Node q );
  /** finish initialize
   *
   * This method sets up final decisions about whether to use single invocation
   * techniques. The argument syntaxRestricted is whether the syntax for
   * solutions for the initialized conjecture is restricted.
   */
  void finishInit(bool syntaxRestricted);
  //check
  bool check( std::vector< Node >& lems );
  //get solution
  Node getSolution( unsigned sol_index, TypeNode stn, int& reconstructed, bool rconsSygus = true );
  //reconstruct to syntax
  Node reconstructToSyntax( Node s, TypeNode stn, int& reconstructed,
                            bool rconsSygus = true );
  // is single invocation
  bool isSingleInvocation() const { return !d_single_inv.isNull(); }
  //needs check
  bool needsCheck();
  /** preregister conjecture */
  void preregisterConjecture( Node q );

  Node getTransPre(Node prog) const {
    std::map<Node, Node>::const_iterator location = d_trans_pre.find(prog);
    return location->second;
  }

  Node getTransPost(Node prog) const {
    std::map<Node, Node>::const_iterator location = d_trans_post.find(prog);
    return location->second;
  }
  // get template for program prog. This returns a term of the form t[x] where x is the template argument (see below)
  Node getTemplate(Node prog) const {
    std::map<Node, Node>::const_iterator tmpl = d_templ.find(prog);
    if( tmpl!=d_templ.end() ){
      return tmpl->second;
    }else{
      return Node::null();
    }
  }
  // get the template argument for program prog.
  // This is a variable which indicates the position of the function/predicate to synthesize.
  Node getTemplateArg(Node prog) const {
    std::map<Node, Node>::const_iterator tmpla = d_templ_arg.find(prog);
    if( tmpla != d_templ_arg.end() ){
      return tmpla->second;
    }else{
      return Node::null();
    }
  }
};

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

#endif
