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
#include "theory/quantifiers/cegqi/ceg_instantiator.h"

#include <unordered_set>

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** TODO (#1367) : document these classes, also move to separate files. */

class ArithInstantiator : public Instantiator {
 public:
  ArithInstantiator( QuantifiersEngine * qe, TypeNode tn ) : Instantiator( qe, tn ){}
  virtual ~ArithInstantiator(){}
  virtual void reset(CegInstantiator* ci,
                     SolvedForm& sf,
                     Node pv,
                     CegInstEffort effort) override;
  virtual bool hasProcessEquality(CegInstantiator* ci,
                                  SolvedForm& sf,
                                  Node pv,
                                  CegInstEffort effort) override
  {
    return true;
  }
  virtual bool processEquality(CegInstantiator* ci,
                               SolvedForm& sf,
                               Node pv,
                               std::vector<TermProperties>& term_props,
                               std::vector<Node>& terms,
                               CegInstEffort effort) override;
  virtual bool hasProcessAssertion(CegInstantiator* ci,
                                   SolvedForm& sf,
                                   Node pv,
                                   CegInstEffort effort) override
  {
    return true;
  }
  virtual Node hasProcessAssertion(CegInstantiator* ci,
                                   SolvedForm& sf,
                                   Node pv,
                                   Node lit,
                                   CegInstEffort effort) override;
  virtual bool processAssertion(CegInstantiator* ci,
                                SolvedForm& sf,
                                Node pv,
                                Node lit,
                                Node alit,
                                CegInstEffort effort) override;
  virtual bool processAssertions(CegInstantiator* ci,
                                 SolvedForm& sf,
                                 Node pv,
                                 CegInstEffort effort) override;
  virtual bool needsPostProcessInstantiationForVariable(
      CegInstantiator* ci,
      SolvedForm& sf,
      Node pv,
      CegInstEffort effort) override;
  virtual bool postProcessInstantiationForVariable(
      CegInstantiator* ci,
      SolvedForm& sf,
      Node pv,
      CegInstEffort effort,
      std::vector<Node>& lemmas) override;
  virtual std::string identify() const override { return "Arith"; }
 private:
  Node d_vts_sym[2];
  std::vector<Node> d_mbp_bounds[2];
  std::vector<Node> d_mbp_coeff[2];
  std::vector<Node> d_mbp_vts_coeff[2][2];
  std::vector<Node> d_mbp_lit[2];
  int solve_arith(CegInstantiator* ci,
                  Node v,
                  Node atom,
                  Node& veq_c,
                  Node& val,
                  Node& vts_coeff_inf,
                  Node& vts_coeff_delta);
  Node getModelBasedProjectionValue(CegInstantiator* ci,
                                    Node e,
                                    Node t,
                                    bool isLower,
                                    Node c,
                                    Node me,
                                    Node mt,
                                    Node theta,
                                    Node inf_coeff,
                                    Node delta_coeff);
};

class DtInstantiator : public Instantiator {
public:
  DtInstantiator( QuantifiersEngine * qe, TypeNode tn ) : Instantiator( qe, tn ){}
  virtual ~DtInstantiator(){}
  virtual void reset(CegInstantiator* ci,
                     SolvedForm& sf,
                     Node pv,
                     CegInstEffort effort) override;
  virtual bool processEqualTerms(CegInstantiator* ci,
                                 SolvedForm& sf,
                                 Node pv,
                                 std::vector<Node>& eqc,
                                 CegInstEffort effort) override;
  virtual bool hasProcessEquality(CegInstantiator* ci,
                                  SolvedForm& sf,
                                  Node pv,
                                  CegInstEffort effort) override
  {
    return true;
  }
  virtual bool processEquality(CegInstantiator* ci,
                               SolvedForm& sf,
                               Node pv,
                               std::vector<TermProperties>& term_props,
                               std::vector<Node>& terms,
                               CegInstEffort effort) override;
  virtual std::string identify() const override { return "Dt"; }
 private:
  Node solve_dt(Node v, Node a, Node b, Node sa, Node sb);
};

class TermArgTrie;

class EprInstantiator : public Instantiator {
 public:
  EprInstantiator( QuantifiersEngine * qe, TypeNode tn ) : Instantiator( qe, tn ){}
  virtual ~EprInstantiator(){}
  virtual void reset(CegInstantiator* ci,
                     SolvedForm& sf,
                     Node pv,
                     CegInstEffort effort) override;
  virtual bool processEqualTerm(CegInstantiator* ci,
                                SolvedForm& sf,
                                Node pv,
                                TermProperties& pv_prop,
                                Node n,
                                CegInstEffort effort) override;
  virtual bool processEqualTerms(CegInstantiator* ci,
                                 SolvedForm& sf,
                                 Node pv,
                                 std::vector<Node>& eqc,
                                 CegInstEffort effort) override;
  virtual std::string identify() const override { return "Epr"; }
 private:
  std::vector<Node> d_equal_terms;
  void computeMatchScore(CegInstantiator* ci,
                         Node pv,
                         Node catom,
                         std::vector<Node>& arg_reps,
                         TermArgTrie* tat,
                         unsigned index,
                         std::map<Node, int>& match_score);
  void computeMatchScore(CegInstantiator* ci,
                         Node pv,
                         Node catom,
                         Node eqc,
                         std::map<Node, int>& match_score);
};

/** Bitvector instantiator
 *
 * This implements an approach for counterexample-guided instantiation
 * for bit-vector variables based on word-level inversions.
 * It is enabled by --cbqi-bv.
 */
class BvInstantiator : public Instantiator {
 public:
  BvInstantiator(QuantifiersEngine* qe, TypeNode tn);
  ~BvInstantiator() override;
  void reset(CegInstantiator* ci,
             SolvedForm& sf,
             Node pv,
             CegInstEffort effort) override;
  bool hasProcessAssertion(CegInstantiator* ci,
                           SolvedForm& sf,
                           Node pv,
                           CegInstEffort effort) override
  {
    return true;
  }
  Node hasProcessAssertion(CegInstantiator* ci,
                           SolvedForm& sf,
                           Node pv,
                           Node lit,
                           CegInstEffort effort) override;
  bool processAssertion(CegInstantiator* ci,
                        SolvedForm& sf,
                        Node pv,
                        Node lit,
                        Node alit,
                        CegInstEffort effort) override;
  bool processAssertions(CegInstantiator* ci,
                         SolvedForm& sf,
                         Node pv,
                         CegInstEffort effort) override;
  /** use model value
   *
   * We allow model values if we have not already tried an assertion,
   * and only at levels below full if cbqiFullEffort is false.
   */
  bool useModelValue(CegInstantiator* ci,
                     SolvedForm& sf,
                     Node pv,
                     CegInstEffort effort) override;
  std::string identify() const override { return "Bv"; }

 private:
  // point to the bv inverter class
  BvInverter * d_inverter;
  unsigned d_inst_id_counter;
  /** information about solved forms */
  std::unordered_map< Node, std::vector< unsigned >, NodeHashFunction > d_var_to_inst_id;
  std::unordered_map< unsigned, Node > d_inst_id_to_term;
  std::unordered_map<unsigned, Node> d_inst_id_to_alit;
  // variable to current id we are processing
  std::unordered_map< Node, unsigned, NodeHashFunction > d_var_to_curr_inst_id;
  /** the amount of slack we added for asserted literals */
  std::unordered_map<Node, Node, NodeHashFunction> d_alit_to_model_slack;
  /** whether we have tried an instantiation based on assertion in this round */
  bool d_tried_assertion_inst;
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
  void processLiteral(CegInstantiator* ci,
                      SolvedForm& sf,
                      Node pv,
                      Node lit,
                      Node alit,
                      CegInstEffort effort);
};

/** Bitvector instantiator preprocess
 *
 * This class implements preprocess techniques that are helpful for
 * counterexample-guided instantiation, such as introducing variables
 * that refer to disjoint bit-vector extracts.
 */
class BvInstantiatorPreprocess : public InstantiatorPreprocess
{
 public:
  BvInstantiatorPreprocess() {}
  ~BvInstantiatorPreprocess() override {}
  /** register counterexample lemma
   *
   * This method modifies the contents of lems based on the extract terms
   * it contains when the option --cbqi-bv-rm-extract is enabled. It introduces
   * a dummy equality so that segments of terms t under extracts can be solved
   * independently.
   *
   * For example:
   *   P[ ((extract 7 4) t), ((extract 3 0) t)]
   *     becomes:
   *   P[((extract 7 4) t), ((extract 3 0) t)] ^
   *   t = concat( x74, x30 )
   * where x74 and x30 are fresh variables of type BV_4.
   *
   * Another example:
   *   P[ ((extract 7 3) t), ((extract 4 0) t)]
   *     becomes:
   *   P[((extract 7 4) t), ((extract 3 0) t)] ^
   *   t = concat( x75, x44, x30 )
   * where x75, x44 and x30 are fresh variables of type BV_3, BV_1, and BV_4
   * respectively.
   *
   * Notice we leave the original conjecture alone. This is done for performance
   * since the added equalities ensure we are able to construct the proper
   * solved forms for variables in t and for the intermediate variables above.
   */
  void registerCounterexampleLemma(std::vector<Node>& lems,
                                   std::vector<Node>& ce_vars) override;

 private:
  /** collect extracts
   *
   * This method collects all extract terms in lem
   * and stores them in d_extract_map.
   * visited is the terms we've already visited.
   */
  void collectExtracts(Node lem,
                       std::map<Node, std::vector<Node> >& extract_map,
                       std::unordered_set<TNode, TNodeHashFunction>& visited);
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif
