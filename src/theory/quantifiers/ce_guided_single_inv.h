/*********************                                                        */
/*! \file ce_guided_single_inv.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
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

class CegConjectureSingleInv {
 private:
  friend class CegqiOutputSingleInv;
  // for recognizing templates for invariant synthesis
  Node substituteInvariantTemplates(
      Node n, std::map<Node, Node>& prog_templ,
      std::map<Node, std::vector<Node> >& prog_templ_vars);
  // partially single invocation
  Node removeDeepEmbedding( Node n, std::vector< Node >& progs,
                            std::vector< TypeNode >& types, int& type_valid,
                            std::map< Node, Node >& visited );
  Node addDeepEmbedding( Node n, std::map< Node, Node >& visited );
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
  SingleInvocationPartition* d_sip;
  CegConjectureSingleInvSol* d_sol;
  CegEntailmentInfer* d_ei;
  // the instantiator
  CegqiOutputSingleInv* d_cosi;
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
 public:
  CegConjectureSingleInv( QuantifiersEngine * qe, CegConjecture * p );
  ~CegConjectureSingleInv();
  // original conjecture
  Node d_quant;
  // single invocation portion of quantified formula
  Node d_single_inv;
  Node d_si_guard;
  // non-single invocation portion of quantified formula
  Node d_nsingle_inv;
  Node d_ns_guard;
  // full version quantified formula
  Node d_full_inv;
  Node d_full_guard;
  //explanation for current single invocation conjecture
  Node d_single_inv_exp;
  // transition relation version per program
  std::map< Node, Node > d_trans_pre;
  std::map< Node, Node > d_trans_post;
  std::map< Node, std::vector< Node > > d_prog_templ_vars;
  //the non-single invocation portion of the quantified formula
  std::map< Node, Node > d_nsi_op_map;
  std::map< Node, Node > d_nsi_op_map_to_prog;
  std::map< Node, Node > d_prog_to_eval_op;
 public:
  //get the single invocation lemma(s)
  void getInitialSingleInvLemma( std::vector< Node >& lems );
  //initialize
  void initialize( Node q );
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
  // is single invocation
  bool isFullySingleInvocation() const {
    return !d_single_inv.isNull() && d_nsingle_inv.isNull();
  }
  //needs check
  bool needsCheck();
  /** preregister conjecture */
  void preregisterConjecture( Node q );
  //initialize next candidate si conjecture (if not fully single invocation)
  void initializeNextSiConjecture();

  Node getTransPre(Node prog) const {
    std::map<Node, Node>::const_iterator location = d_trans_pre.find(prog);
    return location->second;
  }

  Node getTransPost(Node prog) const {
    std::map<Node, Node>::const_iterator location = d_trans_post.find(prog);
    return location->second;
  }

};

// partitions any formulas given to it into single invocation/non-single
// invocation only processes functions having argument types exactly matching
// "d_arg_types",  and all invocations are in the same order across all
// functions
class SingleInvocationPartition {
 private:
  //options
  Kind d_checkKind;
  bool inferArgTypes( Node n, std::vector< TypeNode >& typs, std::map< Node, bool >& visited );
  void process( Node n );
  bool collectConjuncts( Node n, bool pol, std::vector< Node >& conj );
  bool processConjunct( Node n, std::map< Node, bool >& visited, std::vector< Node >& args,
                        std::vector< Node >& terms, std::vector< Node >& subs );
  Node getSpecificationInst( Node n, std::map< Node, Node >& lam, std::map< Node, Node >& visited );
  void extractInvariant2( Node n, Node& func, int& pol, std::vector< Node >& disjuncts, bool hasPol, std::map< Node, bool >& visited );
public:
  SingleInvocationPartition( Kind checkKind = kind::APPLY_UF ) : d_checkKind( checkKind ){}
  ~SingleInvocationPartition(){}
  bool init( Node n );
  bool init( std::vector< TypeNode >& typs, Node n );

  //outputs (everything is with bound var)
  std::vector< TypeNode > d_arg_types;
  std::map< Node, bool > d_funcs;
  std::map< Node, Node > d_func_inv;
  std::map< Node, Node > d_inv_to_func;
  std::map< Node, Node > d_func_fo_var;
  std::map< Node, Node > d_fo_var_to_func;
  std::vector< Node > d_func_vars; //the first-order variables corresponding to all functions
  std::vector< Node > d_si_vars;   //the arguments that we based the anti-skolemization on
  std::vector< Node > d_all_vars;  //every free variable of conjuncts[2]
  // si, nsi, all, non-ground si
  std::vector< Node > d_conjuncts[4];

  bool isAntiSkolemizableType( Node f );

  Node getConjunct( int index );
  Node getSingleInvocation() { return getConjunct( 0 ); }
  Node getNonSingleInvocation() { return getConjunct( 1 ); }
  Node getFullSpecification() { return getConjunct( 2 ); }

  Node getSpecificationInst( int index, std::map< Node, Node >& lam );

  void extractInvariant( Node n, Node& func, int& pol, std::vector< Node >& disjuncts );

  bool isPurelySingleInvocation() { return d_conjuncts[1].empty(); }
  bool isNonGroundSingleInvocation() { return d_conjuncts[3].size()==d_conjuncts[1].size(); }

  void debugPrint( const char * c );
};

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

#endif
