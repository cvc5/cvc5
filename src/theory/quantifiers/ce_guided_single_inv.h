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

namespace CVC4 {
namespace theory {
namespace quantifiers {

class CegConjecture;

class CegConjectureSingleInv
{
private:
  CegConjecture * d_parent;
  bool analyzeSygusConjunct( Node n, Node p, std::map< Node, std::vector< Node > >& children,
                            std::map< Node, std::map< Node, std::vector< Node > > >& prog_invoke,
                            std::vector< Node >& progs, std::map< Node, std::map< Node, bool > >& contains, bool pol );
  bool analyzeSygusTerm( Node n, std::map< Node, std::vector< Node > >& prog_invoke, std::map< Node, bool >& contains );
  bool processSingleInvLiteral( Node lit, bool pol, std::map< Node, std::vector< Node > >& case_vals );
  bool doVariableElimination( Node v, std::vector< Node >& conjuncts );
  bool getVariableEliminationTerm( bool pol, bool active, Node v, Node n, TNode& s, int& status );

  Node constructSolution( unsigned i, unsigned index );
  int classifyTerm( Node n, std::map< Node, int >& subs_from_model );
  void collectProgVars( Node n, std::vector< Node >& vars );
  Node applyProgVarSubstitution( Node n, std::map< Node, int >& subs_from_model, std::vector< Node >& subs );

  bool debugSolution( Node sol );
  void debugTermSize( Node sol, int& t_size, int& num_ite );
public:
  CegConjectureSingleInv( Node q, CegConjecture * p );
  // original conjecture
  Node d_quant;
  // single invocation version of quant
  Node d_single_inv;
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
  // solution
  Node d_orig_solution;
  Node d_solution;
public:
  //get the single invocation lemma
  Node getSingleInvLemma( Node guard );
  //initialize
  void initialize();
  //check
  void check( QuantifiersEngine * qe, std::vector< Node >& lems );
  //get solution
  Node getSolution( unsigned i, Node varList );
};

}
}
}

#endif
