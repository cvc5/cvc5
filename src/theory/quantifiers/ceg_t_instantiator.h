/*********************                                                        */
/*! \file ceg_t_instantiator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief theory-specific counterexample-guided quantifier instantiation
 **/


#include "cvc4_private.h"

#ifndef __CVC4__CEG_T_INSTANTIATOR_H
#define __CVC4__CEG_T_INSTANTIATOR_H

#include "theory/quantifiers/bv_inverter.h"
#include "theory/quantifiers/ceg_instantiator.h"

#include <unordered_set>

namespace CVC4 {
namespace theory {
namespace quantifiers {

class ArithInstantiator : public Instantiator {
private:
  Node d_vts_sym[2];
  std::vector< Node > d_mbp_bounds[2];
  std::vector< Node > d_mbp_coeff[2];
  std::vector< Node > d_mbp_vts_coeff[2][2];
  std::vector< Node > d_mbp_lit[2];
  int solve_arith( CegInstantiator * ci, Node v, Node atom, Node & veq_c, Node & val, Node& vts_coeff_inf, Node& vts_coeff_delta );
  Node getModelBasedProjectionValue( CegInstantiator * ci, Node e, Node t, bool isLower, Node c, Node me, Node mt, Node theta, Node inf_coeff, Node delta_coeff );
public:
  ArithInstantiator( QuantifiersEngine * qe, TypeNode tn ) : Instantiator( qe, tn ){}
  virtual ~ArithInstantiator(){}
  void reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort );
  bool hasProcessEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }
  bool processEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< TermProperties >& term_props, std::vector< Node >& terms, unsigned effort );
  bool hasProcessAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }
  Node hasProcessAssertion(CegInstantiator* ci, SolvedForm& sf, Node pv,
                           Node lit, unsigned effort);
  bool processAssertion(CegInstantiator* ci, SolvedForm& sf, Node pv, Node lit,
                        Node alit, unsigned effort);
  bool processAssertions(CegInstantiator* ci, SolvedForm& sf, Node pv,
                         unsigned effort);
  bool needsPostProcessInstantiationForVariable( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort );
  bool postProcessInstantiationForVariable( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort, std::vector< Node >& lemmas );
  std::string identify() const { return "Arith"; }
};

class DtInstantiator : public Instantiator {
private:
  Node solve_dt( Node v, Node a, Node b, Node sa, Node sb );
public:
  DtInstantiator( QuantifiersEngine * qe, TypeNode tn ) : Instantiator( qe, tn ){}
  virtual ~DtInstantiator(){}
  void reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort );
  bool processEqualTerms( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& eqc, unsigned effort );
  bool hasProcessEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }
  bool processEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< TermProperties >& term_props, std::vector< Node >& terms, unsigned effort );
  std::string identify() const { return "Dt"; }
};

class TermArgTrie;

class EprInstantiator : public Instantiator {
private:
  std::vector< Node > d_equal_terms;
  void computeMatchScore( CegInstantiator * ci, Node pv, Node catom, std::vector< Node >& arg_reps, TermArgTrie * tat, unsigned index, std::map< Node, int >& match_score );
  void computeMatchScore( CegInstantiator * ci, Node pv, Node catom, Node eqc, std::map< Node, int >& match_score );
public:
  EprInstantiator( QuantifiersEngine * qe, TypeNode tn ) : Instantiator( qe, tn ){}
  virtual ~EprInstantiator(){}
  void reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort );
  bool processEqualTerm( CegInstantiator * ci, SolvedForm& sf, Node pv, TermProperties& pv_prop, Node n, unsigned effort );
  bool processEqualTerms( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& eqc, unsigned effort );
  std::string identify() const { return "Epr"; }
};


class BvInstantiator : public Instantiator {
private:
  // point to the bv inverter class
  BvInverter * d_inverter;
  unsigned d_inst_id_counter;
  /** information about solved forms */
  std::unordered_map< Node, std::vector< unsigned >, NodeHashFunction > d_var_to_inst_id;
  std::unordered_map< unsigned, Node > d_inst_id_to_term;
  std::unordered_map< unsigned, BvInverterStatus > d_inst_id_to_status;
  std::unordered_map<unsigned, Node> d_inst_id_to_alit;
  // variable to current id we are processing
  std::unordered_map< Node, unsigned, NodeHashFunction > d_var_to_curr_inst_id;
  /** the amount of slack we added for asserted literals */
  std::unordered_map<Node, Node, NodeHashFunction> d_alit_to_model_slack;
  /** rewrite assertion for solve pv
  * returns a literal that is equivalent to lit that leads to best solved form for pv
  */
  Node rewriteAssertionForSolvePv(CegInstantiator* ci, Node pv, Node lit);
  /** rewrite term for solve pv
   * This is a helper function for rewriteAssertionForSolvePv.
   * If this returns non-null value ret, then this indicates
   * that n should be rewritten to ret. It is called as
   * a "post-rewrite", that is, after the children of n
   * have been rewritten and stored in the vector children.
   *
   * contains_pv stores whether certain nodes contain pv.
   * where we guarantee that all subterms of terms in children
   * appear in the domain of contains_pv.
   */
  Node rewriteTermForSolvePv(
      Node pv,
      Node n,
      std::vector<Node>& children,
      std::unordered_map<TNode, bool, TNodeHashFunction>& contains_pv);
  /** process literal, called from processAssertion
  * lit is the literal to solve for pv that has been rewritten according to
  * internal rules here.
  * alit is the asserted literal that lit is derived from.
  */
  void processLiteral(CegInstantiator* ci, SolvedForm& sf, Node pv, Node lit,
                      Node alit, unsigned effort);

 public:
  BvInstantiator( QuantifiersEngine * qe, TypeNode tn );
  virtual ~BvInstantiator();
  void reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort );
  bool hasProcessAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }
  Node hasProcessAssertion(CegInstantiator* ci, SolvedForm& sf, Node pv,
                           Node lit, unsigned effort);
  bool processAssertion(CegInstantiator* ci, SolvedForm& sf, Node pv, Node lit,
                        Node alit, unsigned effort);
  bool processAssertions(CegInstantiator* ci, SolvedForm& sf, Node pv,
                         unsigned effort);
  bool useModelValue( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }
  std::string identify() const { return "Bv"; }
};


}
}
}

#endif
