/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Counterexample-guided quantifier instantiation.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_CEGQI_H
#define CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_CEGQI_H

#include "smt/env_obj.h"
#include "theory/decision_manager.h"
#include "theory/quantifiers/bv_inverter.h"
#include "theory/quantifiers/cegqi/ceg_instantiator.h"
#include "theory/quantifiers/cegqi/nested_qe.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quant_module.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class InstStrategyCegqi;

/**
 * An instantiation rewriter based on the counterexample-guided instantiation
 * quantifiers module below.
 */
class InstRewriterCegqi : public InstantiationRewriter
{
 public:
  InstRewriterCegqi(InstStrategyCegqi* p);
  ~InstRewriterCegqi() {}
  /**
   * Rewrite the instantiation via d_parent, based on virtual term substitution
   * and nested quantifier elimination. Returns a TrustNode of kind REWRITE,
   * corresponding to the rewrite and its proof generator.
   */
  TrustNode rewriteInstantiation(Node q,
                                 const std::vector<Node>& terms,
                                 Node inst,
                                 bool doVts) override;

 private:
  /** pointer to the parent of this class */
  InstStrategyCegqi* d_parent;
};

/**
 * Counterexample-guided quantifier instantiation module.
 *
 * This class manages counterexample-guided instantiation strategies for all
 * asserted quantified formulas.
 */
class InstStrategyCegqi : public QuantifiersModule
{
  typedef context::CDHashSet<Node> NodeSet;
  typedef context::CDHashMap<Node, int> NodeIntMap;

 public:
  InstStrategyCegqi(Env& env,
                    QuantifiersState& qs,
                    QuantifiersInferenceManager& qim,
                    QuantifiersRegistry& qr,
                    TermRegistry& tr);
  ~InstStrategyCegqi();

  /** whether to do counterexample-guided instantiation for quantifier q */
  bool doCbqi(Node q);
  /** needs check at effort */
  bool needsCheck(Theory::Effort e) override;
  /** needs model at effort */
  QEffort needsModel(Theory::Effort e) override;
  /** reset round */
  void reset_round(Theory::Effort e) override;
  /** check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** check complete */
  bool checkComplete(IncompleteId& incId) override;
  /** check complete for quantified formula */
  bool checkCompleteFor(Node q) override;
  /** check ownership */
  void checkOwnership(Node q) override;
  /** identify */
  std::string identify() const override { return std::string("Cegqi"); }
  /** get instantiator for quantifier */
  CegInstantiator* getInstantiator(Node q);
  /** pre-register quantifier */
  void preRegisterQuantifier(Node q) override;

  /**
   * Rewrite the instantiation inst of quantified formula q for terms; return
   * the result.
   *
   * We rewrite inst based on virtual term substitution and nested quantifier
   * elimination. For details, see "Solving Quantified Linear Arithmetic via
   * Counterexample-Guided Instantiation" FMSD 2017, Reynolds et al.
   *
   * Returns a TrustNode of kind REWRITE, corresponding to the rewrite and its
   * proof generator.
   */
  TrustNode rewriteInstantiation(Node q,
                                 const std::vector<Node>& terms,
                                 Node inst,
                                 bool doVts);
  /** get the instantiation rewriter object */
  InstantiationRewriter* getInstRewriter() const;

 protected:
  /** The instantiation rewriter object */
  std::unique_ptr<InstRewriterCegqi> d_irew;
  /** set quantified formula inactive
   *
   * This flag is set to true during a full effort check if at least one
   * quantified formula is set "inactive", that is, its negation is
   * unsatisfiable in the current context.
   */
  bool d_cbqi_set_quant_inactive;
  /** incomplete check
   *
   * This is set to true during a full effort check if this strategy could
   * not find an instantiation for at least one asserted quantified formula.
   */
  bool d_incomplete_check;
  /** whether we have added cbqi lemma */
  NodeSet d_added_cbqi_lemma;
  /** parent guards */
  std::map< Node, std::vector< Node > > d_parent_quant;
  std::map< Node, std::vector< Node > > d_children_quant;
  std::map< Node, bool > d_active_quant;
  /** Whether cegqi handles each quantified formula. */
  std::map<Node, CegHandledStatus> d_do_cbqi;
  /**
   * The instantiator for each quantified formula q registered to this class.
   * This object is responsible for finding instantiatons for q.
   */
  std::map<Node, std::unique_ptr<CegInstantiator>> d_cinst;
  /**
   * The decision strategy for each quantified formula q registered to this
   * class.
   */
  std::map<Node, std::unique_ptr<DecisionStrategy>> d_dstrat;
  /** the current quantified formula we are processing */
  Node d_curr_quant;
  //---------------------- for vts delta minimization
  /**
   * Whether we will use vts delta minimization. If this flag is true, we
   * add lemmas on demand of the form delta < c^1, delta < c^2, ... where c
   * is a small (< 1) constant. This heuristic is used in strategies where
   * vts delta cannot be fully eliminated from assertions (for example, when
   * using nested quantifiers and a non-innermost instantiation strategy).
   * The same strategy applies for vts infinity, which we add lemmas of the
   * form inf > (1/c)^1, inf > (1/c)^2, ....
   */
  bool d_check_vts_lemma_lc;
  /** a multiplier used to make d_small_const even smaller over time */
  const Node d_small_const_multiplier;
  /** a small constant, used as a coefficient above */
  Node d_small_const;
  /** whether we have initialized the lower bound on the free delta */
  context::CDO<bool> d_freeDeltaLb;
  //---------------------- end for vts delta minimization
  /** register ce lemma */
  bool registerCbqiLemma( Node q );
  /** register counterexample lemma
   *
   * This is called when we have constructed lem, the negation of the body of
   * quantified formula q, skolemized with the instantiation constants of q.
   * This function is used for setting up the proper information in the
   * instantiator for q.
   */
  void registerCounterexampleLemma(Node q, Node lem);
  /** has added cbqi lemma */
  bool hasAddedCbqiLemma( Node q ) { return d_added_cbqi_lemma.find( q )!=d_added_cbqi_lemma.end(); }
  /**
   * Return true if q can be processed with nested quantifier elimination.
   * This may add a lemma on the output channel of quantifiers engine if so.
   *
   * @param q The quantified formula to process
   * @param isPreregister Whether this method is being called at preregister.
   */
  bool processNestedQe(Node q, bool isPreregister);
  /** process functions */
  void process(Node q, Theory::Effort effort, int e);
  /**
   * Get counterexample literal. This is the fresh Boolean variable whose
   * semantics is "there exists a set of values for which the body of
   * quantified formula q does not hold". These literals are cached by this
   * class.
   */
  Node getCounterexampleLiteral(Node q);
  /** map from universal quantifiers to their counterexample literals */
  std::map<Node, Node> d_ce_lit;
  /** The nested quantifier elimination utility */
  std::unique_ptr<NestedQe> d_nestedQe;
};

}
}
}  // namespace cvc5::internal

#endif
