/*********************                                                        */
/*! \file ce_guided_single_inv_sol.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for reconstructing solutions for single invocation synthesis conjectures
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CE_GUIDED_SINGLE_INV_SOL_H
#define CVC4__THEORY__QUANTIFIERS__CE_GUIDED_SINGLE_INV_SOL_H

#include <map>
#include <vector>

#include "context/cdhashmap.h"
#include "expr/dtype.h"
#include "expr/node.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

class CegSingleInv;

/** CegSingleInvSol
 *
 * This function implements Figure 5 of "Counterexample-Guided Quantifier
 * Instantiation for Synthesis in SMT", Reynolds et al CAV 2015.
 *
 */
class CegSingleInvSol
{
  friend class CegSingleInv;

 private:
  QuantifiersEngine * d_qe;
  std::vector< Node > d_varList;
  std::map< Node, int > d_dterm_size;
  std::map< Node, int > d_dterm_ite_size;
//solution simplification
private:
  bool debugSolution( Node sol );
  void debugTermSize( Node sol, int& t_size, int& num_ite );

 public:
  CegSingleInvSol(QuantifiersEngine* qe);
  /** reconstruct solution
   *
   * Returns (if possible) a node that is equivalent to sol those syntax
   * matches the grammar corresponding to sygus datatype stn.
   * The value reconstructed is set to 1 if we successfully return a node,
   * otherwise it is set to -1.
   *
   * This method quickly tries to match sol to the grammar induced by stn. If
   * this fails, we use enumerative techniques to try to repair the solution.
   * The number of iterations for this enumeration is bounded by the argument
   * enumLimit if it is positive, and unbounded otherwise.
   */
  Node reconstructSolution(Node sol,
                           TypeNode stn,
                           int& reconstructed,
                           int enumLimit);
  /** preregister conjecture
   *
   * q : the synthesis conjecture this class is for.
   * This is used as a heuristic to find terms in the original conjecture which
   * may be helpful for using during reconstruction.
   */
  void preregisterConjecture(Node q);

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
  bool collectReconstructNodes(int pid,
                               std::vector<Node>& ts,
                               const DTypeConstructor& dtc,
                               std::vector<int>& ids,
                               int& status);
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
  /** list of constructor indices whose operators are identity functions */
  std::map<TypeNode, std::vector<int> > d_id_funcs;
  /** initialize the above information for sygus type tn */
  void registerType(TypeNode tn);
  /** get generic base
   *
   * This returns the builtin term that is the analog of an application of the
   * c^th constructor of dt to fresh variables.
   */
  Node getGenericBase(TypeNode tn, const DType& dt, int c);
  /** cache for the above function */
  std::map<TypeNode, std::map<int, Node> > d_generic_base;
  /** get match
   *
   * This function attempts to find a substitution for which p = n. If
   * successful, this function returns a substitution in the form of s/new_s,
   * where:
   * s : substitution, where the domain are indices of terms in the sygus
   * term database, and
   * new_s : the members that were added to s on this call.
   * Otherwise, this function returns false and s and new_s are unmodified.
   */
  bool getMatch(Node p,
                Node n,
                std::map<int, Node>& s,
                std::vector<int>& new_s);
  /** get match
   *
   * This function attempts to find a builtin term that is analog to a value
   * of the sygus datatype st that is equivalent to n. If this function returns
   * true, then it has found such a term. Then we set:
   *   index_found : updated to the constructor index of the sygus term whose
   *   analog to equivalent to n.
   *   args : builtin terms corresponding to the match, in order.
   * Otherwise, this function returns false and index_found and args are
   * unmodified.
   * For example, for grammar:
   *   A -> 0 | 1 | x | +( A, A )
   * Given input ( 5 + (x+1) ) and A we would return true, where:
   *   index_found is set to 3 and args is set to { 5, x+1 }.
   *
   * index_exc : (if applicable) exclude a constructor index of st
   * index_start : start index of constructors of st to try
   */
  bool getMatch(Node n,
                TypeNode st,
                int& index_found,
                std::vector<Node>& args,
                int index_exc = -1,
                int index_start = 0);
  /** given a term, construct an equivalent smaller one that respects syntax */
  Node minimizeBuiltinTerm(Node n);
  /**
   * Return the kind of "is less than" for type tn, where tn is either Int or
   * BV.
   */
  static Kind getComparisonKind(TypeNode tn);
  /**
   * Return the kind of "plus" for type tn, or "minus" if is_neg is true, where
   * tn is either Int or BV.
   */
  static Kind getPlusKind(TypeNode tn, bool is_neg = false);
};


}
}
}

#endif
