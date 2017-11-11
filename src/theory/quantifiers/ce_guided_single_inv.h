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

#include "context/cdhashmap.h"
#include "context/cdchunk_list.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/ce_guided_single_inv_sol.h"
#include "theory/quantifiers/inst_strategy_cbqi.h"

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


class SingleInvocationPartition;

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

/** single invocation partition
 *
 * This is a utility to group formulas into single invocation/non-single
 * invocation parts, relative to a set of "input functions". 
 * It can be used when either the set of input functions is fixed,
 * or is unknown. 
 * 
 * (EX1) For example, if input functions are { f }, 
 * then the formula is ( f( x, y ) = g( y ) V f( x, y ) = b )
 * is single invocation since there is only one
 * unique application of f, that is, f( x, y ).
 * 
 * When handling multiple input functions, we only infer a formula
 * is single invocation if all (relevant) input functions have the
 * same argument types. An input function is relevant if it is 
 * specified by the input in a call to init() or occurs in the 
 * formula we are processing.
 * 
 * 
 */
class SingleInvocationPartition {
public:
  SingleInvocationPartition() : d_has_input_funcs( false ){}
  ~SingleInvocationPartition(){}
  /** initialize this partition for formula n, with input functions funcs 
   * 
   * This initializes this class to check whether formula n is single 
   * invocation with respect to the input functions in funcs only.
   * Below, we call n the "processed formula".
   * 
   * This method returns true if all input functions have identical 
   * argument type lists.
   */
  bool init( std::vector< Node >& funcs, Node n );
  /** initialize this partition for formula n
   * 
   * In contrast to the above method, this version assumes that
   * all uninterpreted functions are input functions. That is, this
   * method is equivalent to the above function with funcs containing
   * all uninterpreted functions occurring in n.
   */
  bool init( Node n );
  /** is the processed formula purely single invocation? 
   * 
   * A formula is purely single invocation if it is equivalent one of the form:
   *   t[ f1( x ), ..., fn( x ), x ], 
   * where f1...fn are the input functions, where notice that the free 
   * variables of t are exactly x.
   */
  bool isPurelySingleInvocation() { return d_conjuncts[1].empty(); }
  /** is the processed formula non-ground single invocation? 
   *    
   * A formula is non-ground single invocation if it is equivalent one of the form:
   *   t[ f1( x ), ..., fn( x ), x, y ], 
   * where f1...fn are the input functions.
   */
  bool isNonGroundSingleInvocation() { return d_conjuncts[3].size()==d_conjuncts[1].size(); }
  /** Get the (portion of) the processed formula that is single invocation
   * 
   * Notice this method returns the anti-skolemized version of the input formula.
   * In (EX1), this method returns:
   *   z = g( y ) V z = b
   * where z is the first-order variable for f (see getFirstOrderVariableForFunction).
   */
  Node getSingleInvocation() { return getConjunct( 0 ); }
  /** Get the (portion of) the processed formula that is not single invocation
   * 
   * This formula and the above form a partition of the conjuncts of the 
   * processed formula, that is:
   *   getSingleInvocation() * sigma ^ getNonSingleInvocation()
   * is equivalent to the processed formula, where sigma is a substitution of the form:
   *   z_1 -> f_1( x ) .... z_n -> f_n( x )
   * where z_i are the first-order variables for input functions f_i
   * for all i=1,...,n, and x are the single invocation arguments of the input formulas
   * (see d_si_vars).
   */
  Node getNonSingleInvocation() { return getConjunct( 1 ); }
  /** get full specification 
   * 
   * This returns getSingleInvocation() * sigma ^ getNonSingleInvocation(),
   * which is equivalent to the processed formula, where sigma is the substitution
   * described above.
   */
  Node getFullSpecification() { return getConjunct( 2 ); }
  
  /** get first order variable for input function f
   * This corresponds to the variable that we used when anti-skolemized
   * function f. For example, in (EX1), if getSingleInvocation() returns:
   *   z = g( y ) V z = b
   * Then, getFirstOrderVariableForFunction(f) = z.
   */
  Node getFirstOrderVariableForFunction( Node f ) const;
  /** get function for first order variable 
   * Opposite direction of above, where:
   *   getFunctionForFirstOrderVariable(z) = f.
   */
  Node getFunctionForFirstOrderVariable( Node v ) const;
  /** get function invocation for 
   * Returns f( x ) where x are the single invocation arguments of the input formulas
   * (see d_si_vars). If f is not an input function, this returns null.
   */
  Node getFunctionInvocationFor( Node f ) const;
  
  
  /** map from input functions to whether they have an anti-skolemizable type
   * An anti-skolemizable type is one of the form:
   *   ( T1, ..., Tn ) -> T
   * where Ti = d_arg_types[i] for i = 1,...,n.
   */
  std::map< Node, bool > d_funcs;
  /** map from functions to the invocation we inferred for them */
  std::map< Node, Node > d_func_inv;
  /** map from first-order variables to input functions */
  std::vector< Node > d_func_vars;
  /** the arguments that we based the anti-skolemization on 
   * In (EX1), this is the list { x, y }.
   */
  std::vector< Node > d_si_vars;
  /** every free variable of conjuncts[2] */
  std::vector< Node > d_all_vars;
  /** */
  std::map< Node, Node > d_func_fo_var;
  /** map from first-order variables to the function anti-skolemized */
  std::map< Node, Node > d_fo_var_to_func;
  /** The argument types for this single invocation partition.
   * These are the argument types of the input functions we are
   * processing, where notice that:
   *   d_si_vars[i].getType()==d_arg_types[i]
   */
  std::vector< TypeNode > d_arg_types;  
  /** print debugging information on Trace c */
  void debugPrint( const char * c );
private:
  /** the list of conjuncts with various properties :
   * 0 : the single invocation conjuncts (stored in anti-skolemized form),
   * 1 : the non-single invocation conjuncts,
   * 2 : all conjuncts,
   * 3 : non-ground single invocation conjuncts.
   */
  std::vector< Node > d_conjuncts[4];  
  /** did we initialize this class with input functions? */
  bool d_has_input_funcs;
  /** the input functions we initialized this class with */
  std::vector< Node > d_input_funcs;
  /** infer the argument types of uninterpreted function applications 
   * 
   * If this method returns true, then the contents of typs contains
   * the list of types of the arguments (in order) of all uninterpreted 
   * functions in n. 
   * If this method returns false, then there exists (at least) two 
   * uninterpreted functions in n whose argument types are not identical.
   */
  bool inferArgTypes( Node n, std::vector< TypeNode >& typs, std::map< Node, bool >& visited );
  /** is anti-skolemizable type 
   * This method returns true if f's argument types are equal to the 
   * argument types we have fixed in this class (see d_arg_types).
   */
  bool isAntiSkolemizableType( Node f );  
  /** This is the entry point for initializing this class, 
   * which is called by the public init(...) methods.
   *   funcs are the input functions (if any were explicitly provide),
   *   typs is the types of the arguments of funcs,
   *   n is the formula to process,
   *   has_funcs is whether input functions were explicitly provided.
   */
  bool init( std::vector< Node >& funcs, std::vector< TypeNode >& typs, Node n, bool has_funcs );
  /** process the term n 
   * 
   * 
   */
  void process( Node n );
  /** collect the top-level conjuncts of the formula (equivalent to) 
   * n or the negation of n if pol=false, and store them in conj.
   */
  bool collectConjuncts( Node n, bool pol, std::vector< Node >& conj );
  /** process conjunct n
   * 
   */
  bool processConjunct( Node n, std::map< Node, bool >& visited, std::vector< Node >& args,
                        std::vector< Node >& terms, std::vector< Node >& subs );
  /** get the and node corresponding to d_conjuncts[index] */
  Node getConjunct( int index );
};


}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

#endif
