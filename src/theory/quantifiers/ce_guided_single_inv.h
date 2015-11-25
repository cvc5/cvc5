/*********************                                                        */
/*! \file ce_guided_single_inv.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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

class CegqiOutputSingleInv : public CegqiOutput
{
public:
  CegqiOutputSingleInv( CegConjectureSingleInv * out ) : d_out( out ){}
  ~CegqiOutputSingleInv() {}
  CegConjectureSingleInv * d_out;
  bool addInstantiation( std::vector< Node >& subs );
  bool isEligibleForInstantiation( Node n );
  bool addLemma( Node lem );
};


class SingleInvocationPartition;

class CegConjectureSingleInv
{
  friend class CegqiOutputSingleInv;
private:
  SingleInvocationPartition * d_sip;
  QuantifiersEngine * d_qe;
  CegConjecture * d_parent;
  CegConjectureSingleInvSol * d_sol;
  //the instantiator
  CegInstantiator * d_cinst;
  //for recognizing when conjecture is single invocation
  bool analyzeSygusConjunct( Node n, Node p, std::map< Node, std::vector< Node > >& children,
                            std::map< Node, std::map< Node, std::vector< Node > > >& prog_invoke,
                            std::vector< Node >& progs, std::map< Node, std::map< Node, bool > >& contains, bool pol );
  bool analyzeSygusTerm( Node n, std::map< Node, std::vector< Node > >& prog_invoke, std::map< Node, bool >& contains );
  bool processSingleInvLiteral( Node lit, bool pol, std::map< Node, std::vector< Node > >& case_vals );
  bool doVariableElimination( Node v, std::vector< Node >& conjuncts );
  bool getVariableEliminationTerm( bool pol, bool active, Node v, Node n, TNode& s, int& status );
  //for recognizing templates for invariant synthesis
  int extractInvariantPolarity( Node n, Node inv, std::vector< Node >& curr_disj, bool pol );
  Node substituteInvariantTemplates( Node n, std::map< Node, Node >& prog_templ, std::map< Node, std::vector< Node > >& prog_templ_vars );
  // partially single invocation
  Node removeDeepEmbedding( Node n, std::vector< Node >& progs, std::vector< TypeNode >& types, int& type_valid, std::map< Node, Node >& visited );
  //presolve
  void collectPresolveEqTerms( Node n, std::map< Node, std::vector< Node > >& teq );
  void getPresolveEqConjuncts( std::vector< Node >& vars, std::vector< Node >& terms, std::map< Node, std::vector< Node > >& teq, Node n, std::vector< Node >& conj );
  //constructing solution
  Node constructSolution( std::vector< unsigned >& indices, unsigned i, unsigned index );
private:
  //map from programs to variables in single invocation property
  std::map< Node, Node > d_single_inv_map;
  std::map< Node, Node > d_single_inv_map_to_prog;
  //map from programs to evaluator term representing the above variable
  std::map< Node, Node > d_single_inv_app_map;
  //list of skolems for each argument of programs
  std::vector< Node > d_single_inv_arg_sk;
  //list of variables/skolems for each program
  std::vector< Node > d_single_inv_var;
  std::vector< Node > d_single_inv_sk;
  std::map< Node, int > d_single_inv_sk_index;
  //program to solution index
  std::map< Node, unsigned > d_prog_to_sol_index;
  //lemmas produced
  inst::InstMatchTrie d_inst_match_trie;
  inst::CDInstMatchTrie * d_c_inst_match_trie;
  //original conjecture
  Node d_orig_conjecture;
  // solution
  std::vector< Node > d_varList;
  Node d_orig_solution;
  Node d_solution;
  Node d_sygus_solution;
  bool d_has_ites;
public:
  //lemmas produced
  std::vector< Node > d_lemmas_produced;
  std::vector< std::vector< Node > > d_inst;
private:
  std::vector< Node > d_curr_lemmas;
  //add instantiation
  bool addInstantiation( std::vector< Node >& subs );
  //is eligible for instantiation
  bool isEligibleForInstantiation( Node n );
  // add lemma
  bool addLemma( Node lem );
public:
  CegConjectureSingleInv( QuantifiersEngine * qe, CegConjecture * p );
  // original conjecture
  Node d_quant;
  // single invocation version of quantified formula
  Node d_single_inv;
  // transition relation version per program
  std::map< Node, Node > d_trans_pre;
  std::map< Node, Node > d_trans_post;
  std::map< Node, std::vector< Node > > d_prog_templ_vars;
  //the non-single invocation portion of the quantified formula
  std::map< Node, Node > d_nsi_op_map;
public:
  //get the single invocation lemma(s)
  void getSingleInvLemma( Node guard, std::vector< Node >& lems );
  //initialize
  void initialize( Node q );
  //check
  void check( std::vector< Node >& lems );
  //get solution
  Node getSolution( unsigned sol_index, TypeNode stn, int& reconstructed );
  //reconstruct to syntax
  Node reconstructToSyntax( Node s, TypeNode stn, int& reconstructed );
  // has ites
  bool hasITEs() { return d_has_ites; }
  // is single invocation
  bool isSingleInvocation() { return !d_single_inv.isNull(); }
  //needs check
  bool needsCheck();
  /** preregister conjecture */
  void preregisterConjecture( Node q );
};

// partitions any formulas given to it into single invocation/non-single invocation
// only processes functions having argument types exactly matching "d_arg_types", 
//   and all invocations are in the same order across all functions
class SingleInvocationPartition
{
private:
  bool collectConjuncts( Node n, bool pol, std::vector< Node >& conj );
  bool processConjunct( Node n, std::map< Node, bool >& visited, std::vector< Node >& args, 
                        std::vector< Node >& terms, std::vector< Node >& subs );
public:
  void init( std::vector< TypeNode >& typs );
  //inputs
  void process( Node n );
  std::vector< TypeNode > d_arg_types;
  
  //outputs (everything is with bound var)
  std::map< Node, bool > d_funcs;
  std::map< Node, Node > d_func_inv;
  std::map< Node, Node > d_func_fo_var;
  std::vector< Node > d_func_vars;
  std::vector< Node > d_si_vars;
  // si, nsi, all
  std::vector< Node > d_conjuncts[3];
  
  bool isAntiSkolemizableType( Node f );
  
  Node getConjunct( int index );
  Node getSingleInvocation() { return getConjunct( 0 ); }
  Node getNonSingleInvocation() { return getConjunct( 1 ); }
  Node getFullSpecification() { return getConjunct( 2 ); }
  
  void debugPrint( const char * c );
};


}
}
}

#endif
