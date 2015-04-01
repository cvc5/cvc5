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

namespace CVC4 {
namespace theory {
namespace quantifiers {

class CegConjecture;

class CegqiOutput
{
public:
  virtual bool addInstantiation( std::vector< Node >& subs, std::vector< int >& subs_typ ) = 0;
  virtual bool isEligibleForInstantiation( Node n ) = 0;
  virtual bool addLemma( Node lem ) = 0;
};

class CegInstantiator
{
private:
  Node d_zero;
  Node d_one;
  Node d_true;
  QuantifiersEngine * d_qe;
  CegqiOutput * d_out;
  //program variable contains cache
  std::map< Node, std::map< Node, bool > > d_prog_var;
  std::map< Node, bool > d_inelig;
  std::map< Node, bool > d_has_delta;
private:
  //for adding instantiations during check
  void computeProgVars( Node n );
  // effort=0 : do not use model value, 1: use model value, 2: one must use model value
  bool addInstantiation( std::vector< Node >& subs, std::vector< Node >& vars,
                         std::vector< Node >& coeff, std::vector< Node >& has_coeff, std::vector< int >& subs_typ,
                         unsigned i, unsigned effort );
  bool addInstantiationInc( Node n, Node pv, Node pv_coeff, int styp, std::vector< Node >& subs, std::vector< Node >& vars,
                            std::vector< Node >& coeff, std::vector< Node >& has_coeff, std::vector< int >& subs_typ,
                            unsigned i, unsigned effort );
  bool addInstantiationCoeff( std::vector< Node >& subs, std::vector< Node >& vars,
                              std::vector< Node >& coeff, std::vector< Node >& has_coeff, std::vector< int >& subs_typ,
                              unsigned j );
  bool addInstantiation( std::vector< Node >& subs, std::vector< Node >& vars, std::vector< int >& subs_typ );
  Node applySubstitution( Node n, std::vector< Node >& subs, std::vector< Node >& vars,
                          std::vector< Node >& coeff, std::vector< Node >& has_coeff, Node& pv_coeff, bool try_coeff = true );
public:
  CegInstantiator( QuantifiersEngine * qe, CegqiOutput * out );
  //the CE variables
  std::vector< Node > d_vars;
  //delta
  Node d_n_delta;
  //check : add instantiations based on valuation of d_vars
  void check();
  // get delta lemmas : on-demand force minimality of d_n_delta
  void getDeltaLemmas( std::vector< Node >& lems );
};


class CegConjectureSingleInv;

class CegqiOutputSingleInv : public CegqiOutput
{
public:
  CegqiOutputSingleInv( CegConjectureSingleInv * out ) : d_out( out ){}
  CegConjectureSingleInv * d_out;
  bool addInstantiation( std::vector< Node >& subs, std::vector< int >& subs_typ );
  bool isEligibleForInstantiation( Node n );
  bool addLemma( Node lem );
};



class CegConjectureSingleInv
{
  friend class CegqiOutputSingleInv;
private:
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
  //constructing solution
  Node constructSolution( unsigned i, unsigned index );
private:
  //map from programs to variables in single invocation property
  std::map< Node, Node > d_single_inv_map;
  std::map< Node, Node > d_single_inv_map_to_prog;
  //map from programs to evaluator term representing the above variable
  std::map< Node, Node > d_single_inv_app_map;
  //list of skolems for each argument of programs
  std::vector< Node > d_single_inv_arg_sk;
  //list of skolems for each program
  std::vector< Node > d_single_inv_sk;
  std::map< Node, int > d_single_inv_sk_index;
  //list of skolems for each program
  std::vector< Node > d_single_inv_var;
  //lemmas produced
  std::vector< Node > d_lemmas_produced;
  std::vector< std::vector< Node > > d_inst;
  inst::InstMatchTrie d_inst_match_trie;
  inst::CDInstMatchTrie * d_c_inst_match_trie;
  // solution
  std::vector< Node > d_varList;
  Node d_orig_solution;
  Node d_solution;
  Node d_sygus_solution;
private:
  std::vector< Node > d_curr_lemmas;
  //add instantiation
  bool addInstantiation( std::vector< Node >& subs, std::vector< int >& subs_typ );
  //is eligible for instantiation
  bool isEligibleForInstantiation( Node n );
  // add lemma
  bool addLemma( Node lem );
public:
  CegConjectureSingleInv( CegConjecture * p );
  // original conjecture
  Node d_quant;
  // single invocation version of quant
  Node d_single_inv;
public:
  //get the single invocation lemma
  Node getSingleInvLemma( Node guard );
  //initialize
  void initialize( QuantifiersEngine * qe, Node q );
  //check
  void check( std::vector< Node >& lems );
  //get solution
  Node getSolution( unsigned sol_index, TypeNode stn, int& reconstructed );
};

}
}
}

#endif
