/*********************                                                        */
/*! \file ceg_bv_instantiator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief ceg_bv_instantiator
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CEG_BV_INSTANTIATOR_H
#define CVC4__THEORY__QUANTIFIERS__CEG_BV_INSTANTIATOR_H

#include <unordered_map>
#include "theory/quantifiers/bv_inverter.h"
#include "theory/quantifiers/cegqi/ceg_instantiator.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Bitvector instantiator
 *
 * This implements an approach for counterexample-guided instantiation
 * for bit-vector variables based on word-level inversions. For details,
 * see Niemetz et al, "Solving Quantified Bit-Vectors Using Invertibility
 * Conditions", CAV 2018. It is enabled by --cbqi-bv.
 *
 * This class contains all necessary information for instantiating a single
 * bit-vector variable of a single quantified formula.
 */
class BvInstantiator : public Instantiator
{
 public:
  BvInstantiator(TypeNode tn, BvInverter* inv);
  ~BvInstantiator() override;
  /** reset */
  void reset(CegInstantiator* ci,
             SolvedForm& sf,
             Node pv,
             CegInstEffort effort) override;
  /** this instantiator processes assertions */
  bool hasProcessAssertion(CegInstantiator* ci,
                           SolvedForm& sf,
                           Node pv,
                           CegInstEffort effort) override;
  /** this instantiator processes bit-vector equalities and inequalities
   *
   * Based on the configuration --cbqi-bv-ineq, it may modify the form of lit
   * based on a projection. For lit (not) s <> t, this may be one of:
   * - eq-slack: s = t + ( s^M - t^M )
   * - eq-boundary: s = t + ( s^M > t^M ? 1 : -1 )
   * - keep: (not) s <> t, i.e. unchanged.
   * Additionally for eq-boundary, inequalities s != t become s < t or t < s.
   * This is the method project_* from Figure 3 of Niemetz et al, CAV 2018.
   */
  Node hasProcessAssertion(CegInstantiator* ci,
                           SolvedForm& sf,
                           Node pv,
                           Node lit,
                           CegInstEffort effort) override;
  /** process assertion
   *
   * Computes a solved form for pv in lit based on Figure 1 of Niemetz et al,
   * CAV 2018.
   */
  bool processAssertion(CegInstantiator* ci,
                        SolvedForm& sf,
                        Node pv,
                        Node lit,
                        Node alit,
                        CegInstEffort effort) override;
  /** process assertions
   *
   * This is called after processAssertion has been called on all currently
   * asserted literals that involve pv. This chooses the best solved form for pv
   * based on heuristics. Currently, by default, we choose a random solved form.
   * We may try multiple or zero bounds based on the options
   * --cbqi-multi-inst and --cbqi-bv-interleave-value.
   */
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
  /** identify */
  std::string identify() const override { return "Bv"; }

 private:
  /** pointer to the bv inverter class */
  BvInverter* d_inverter;
  //--------------------------------solved forms
  /** identifier counter, used to allocate ids to each solve form */
  unsigned d_inst_id_counter;
  /** map from variables to list of solved form ids */
  std::unordered_map<Node, std::vector<unsigned>, NodeHashFunction>
      d_var_to_inst_id;
  /** for each solved form id, the term for instantiation */
  std::unordered_map<unsigned, Node> d_inst_id_to_term;
  /** for each solved form id, the corresponding asserted literal */
  std::unordered_map<unsigned, Node> d_inst_id_to_alit;
  /** map from variable to current id we are processing */
  std::unordered_map<Node, unsigned, NodeHashFunction> d_var_to_curr_inst_id;
  /** the amount of slack we added for asserted literals */
  std::unordered_map<Node, Node, NodeHashFunction> d_alit_to_model_slack;
  //--------------------------------end solved forms
  /** rewrite assertion for solve pv
   *
   * Returns a literal that is equivalent to lit that leads to best solved form
   * for pv.
   */
  Node rewriteAssertionForSolvePv(CegInstantiator* ci, Node pv, Node lit);
  /** rewrite term for solve pv
   *
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
      std::unordered_map<Node, bool, NodeHashFunction>& contains_pv);
  /** process literal, called from processAssertion
   *
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
   * This method adds to auxLems based on the extract terms that lem
   * contains when the option --cbqi-bv-rm-extract is enabled. It introduces
   * a dummy equality so that segments of terms t under extracts can be solved
   * independently.
   *
   * For example, if lem is:
   *   P[ ((extract 7 4) t), ((extract 3 0) t)]
   *     then we add:
   *   t = concat( x74, x30 )
   * to auxLems, where x74 and x30 are fresh variables of type BV_4, which are
   * added to ceVars.
   *
   * Another example, for:
   *   P[ ((extract 7 3) t), ((extract 4 0) t)]
   *     we add:
   *   t = concat( x75, x44, x30 )
   * to auxLems where x75, x44 and x30 are fresh variables of type BV_3, BV_1,
   * and BV_4 respectively, which are added to ceVars.
   *
   * Notice we leave the original lem alone. This is done for performance
   * since the added equalities ensure we are able to construct the proper
   * solved forms for variables in t and for the intermediate variables above.
   */
  void registerCounterexampleLemma(Node lem,
                                   std::vector<Node>& ceVars,
                                   std::vector<Node>& auxLems) override;

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

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__CEG_BV_INSTANTIATOR_H */
