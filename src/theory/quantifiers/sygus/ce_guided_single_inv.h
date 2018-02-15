/*********************                                                        */
/*! \file ce_guided_single_inv.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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
#include "theory/quantifiers/cegqi/inst_strategy_cbqi.h"
#include "theory/quantifiers/single_inv_partition.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class CegConjecture;
class CegConjectureSingleInv;
class CegEntailmentInfer;

class CegqiOutputSingleInv : public CegqiOutput {
public:
  CegqiOutputSingleInv( CegConjectureSingleInv * out ) : d_out( out ){}
  virtual ~CegqiOutputSingleInv() {}
  CegConjectureSingleInv * d_out;
  bool doAddInstantiation( std::vector< Node >& subs );
  bool isEligibleForInstantiation( Node n );
  bool addLemma( Node lem );
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

class TransitionInference {
private:
  bool processDisjunct( Node n, std::map< bool, Node >& terms, std::vector< Node >& disjuncts, std::map< Node, bool >& visited, bool topLevel );
  void getConstantSubstitution( std::vector< Node >& vars, std::vector< Node >& disjuncts, std::vector< Node >& const_var, std::vector< Node >& const_subs, bool reqPol );
  bool d_complete;
public:
  TransitionInference() : d_complete( false ) {}
  std::vector< Node > d_vars;
  std::vector< Node > d_prime_vars;
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
class CegConjectureSingleInv {
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
  QuantifiersEngine* d_qe;
  CegConjecture* d_parent;
  // single invocation inference utility
  SingleInvocationPartition* d_sip;
  // transition inference module for each function to synthesize
  std::map< Node, TransitionInference > d_ti;
  // solution reconstruction
  CegConjectureSingleInvSol* d_sol;
  // the instantiator's output channel
  CegqiOutputSingleInv* d_cosi;
  // the instantiator
  CegInstantiator* d_cinst;

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
  // whether the grammar for our solution allows ITEs, this tells us when reconstruction is infeasible
  bool d_has_ites;

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
  Node d_si_guard;
  // transition relation version per program
  std::map< Node, Node > d_trans_pre;
  std::map< Node, Node > d_trans_post;
  // the template for each function to synthesize
  std::map< Node, Node > d_templ;
  // the template argument for each function to synthesize (occurs in exactly one position of its template)
  std::map< Node, Node > d_templ_arg;
  
 public:
  CegConjectureSingleInv( QuantifiersEngine * qe, CegConjecture * p );
  ~CegConjectureSingleInv();

  // get simplified conjecture
  Node getSimplifiedConjecture() { return d_simp_quant; }
  // get single invocation guard
  Node getGuard() { return d_si_guard; }
 public:
  //get the single invocation lemma(s)
  void getInitialSingleInvLemma( std::vector< Node >& lems );
  // initialize this class for synthesis conjecture q
  void initialize( Node q );
  // finish initialize, sets up final decisions about whether to use single invocation techniques
  //  syntaxRestricted is whether the syntax for solutions for the initialized conjecture is restricted
  //  hasItes is whether the syntax for solutions for the initialized conjecture allows ITEs
  void finishInit( bool syntaxRestricted, bool hasItes );
  //check
  bool check( std::vector< Node >& lems );
  //get solution
  Node getSolution( unsigned sol_index, TypeNode stn, int& reconstructed, bool rconsSygus = true );
  //reconstruct to syntax
  Node reconstructToSyntax( Node s, TypeNode stn, int& reconstructed,
                            bool rconsSygus = true );
  // has ites
  bool hasITEs() { return d_has_ites; }
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
