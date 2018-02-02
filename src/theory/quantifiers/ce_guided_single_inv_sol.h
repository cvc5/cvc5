/*********************                                                        */
/*! \file ce_guided_single_inv_sol.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for reconstructing solutions for single invocation synthesis conjectures
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_SINGLE_INV_SOL_H
#define __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_SINGLE_INV_SOL_H

#include "context/cdhashmap.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {


class CegConjectureSingleInv;

class CegConjectureSingleInvSol
{
  friend class CegConjectureSingleInv;
private:
  QuantifiersEngine * d_qe;
  std::vector< Node > d_varList;
  std::map< Node, int > d_dterm_size;
  std::map< Node, int > d_dterm_ite_size;
//solution simplification
private:
  bool debugSolution( Node sol );
  void debugTermSize( Node sol, int& t_size, int& num_ite );
  Node pullITEs( Node n );
  bool pullITECondition( Node root, Node n, std::vector< Node >& conj, Node& t, Node& rem, int depth );
  Node flattenITEs( Node n, bool rec = true );
  bool getAssign( bool pol, Node n, std::map< Node, bool >& assign, std::vector< Node >& new_assign,
                  std::vector< Node >& vars, std::vector< Node >& new_vars, std::vector< Node >& new_subs );
  bool getAssignEquality( Node eq, std::vector< Node >& vars, std::vector< Node >& new_vars, std::vector< Node >& new_subs );
  Node simplifySolutionNode( Node sol, TypeNode stn, std::map< Node, bool >& assign,
                             std::vector< Node >& vars, std::vector< Node >& subs, int status );
public:
  Node simplifySolution( Node sol, TypeNode stn );
//solution reconstruction
private:
  int d_id_count;
  int d_root_id;
  std::map< int, Node > d_id_node;
  std::map< int, TypeNode > d_id_type;
  std::map< TypeNode, std::map< Node, int > > d_rcons_to_id;
  std::map< TypeNode, std::map< Node, int > > d_rcons_to_status;

  std::map< int, std::map< Node, std::vector< int > > > d_reconstruct_op;
  std::map< int, Node > d_reconstruct;
  std::map< int, std::vector< int > > d_parents;

  std::map< int, std::vector< int > > d_eqc;
  std::map< int, int > d_rep;
  
  //equivalent terms
  std::map< Node, Node > d_eqt_rep;
  std::map< Node, std::vector< Node > > d_eqt_eqc;

  //cache when reconstructing solutions
  std::vector< int > d_tmp_fail;
  // get reconstructed solution
  Node getReconstructedSolution( int id, bool mod_eq = true );

  // allocate node with type
  int allocate( Node n, TypeNode stn );
  // term t with sygus type st, returns inducted templated form of t
  int collectReconstructNodes( Node t, TypeNode stn, int& status );
  bool collectReconstructNodes( int pid, std::vector< Node >& ts, const DatatypeConstructor& dtc, std::vector< int >& ids, int& status );
  bool getPathToRoot( int id );
  void setReconstructed( int id, Node n );
  //get equivalent terms to n with top symbol k
  void getEquivalentTerms( Kind k, Node n, std::vector< Node >& equiv );
  //register equivalent terms
  void registerEquivalentTerms( Node n );
  /** builtin to sygus const
   *
   * Returns a sygus term of type tn that encodes the builtin constant c.
   * If the sygus datatype tn allows any constant, this may return a variable
   * with the attribute SygusPrintProxyAttribute that associates it with c.
   *
   * rcons_depth limits the number of recursive calls when doing accelerated
   * constant reconstruction (currently limited to 1000). Notice this is hacky:
   * depending upon order of calls, constant rcons may succeed, e.g. 1001, 999
   * vs. 999, 1001.
   */
  Node builtinToSygusConst(Node c, TypeNode tn, int rcons_depth = 0);
  /** cache for the above function */
  std::map<TypeNode, std::map<Node, Node> > d_builtin_const_to_sygus;
  /** sorted list of constants, per type */
  std::map<TypeNode, std::vector<Node> > d_const_list;
  /** number of positive constants, per type */
  std::map<TypeNode, unsigned> d_const_list_pos;
  /** initialize the above two lists for sygus type tn */
  void initializeConstLists(TypeNode tn);
 public:
  Node reconstructSolution( Node sol, TypeNode stn, int& reconstructed );
  void preregisterConjecture( Node q );
public:
  CegConjectureSingleInvSol( QuantifiersEngine * qe );
};


}
}
}

#endif
