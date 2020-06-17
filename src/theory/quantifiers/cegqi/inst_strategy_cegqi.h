/*********************                                                        */
/*! \file inst_strategy_cegqi.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief counterexample-guided quantifier instantiation
 **/


#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__INST_STRATEGY_CEGQI_H
#define CVC4__THEORY__QUANTIFIERS__INST_STRATEGY_CEGQI_H

#include "theory/decision_manager.h"
#include "theory/quantifiers/bv_inverter.h"
#include "theory/quantifiers/cegqi/ceg_instantiator.h"
#include "theory/quantifiers/cegqi/vts_term_cache.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quant_util.h"
#include "util/statistics_registry.h"

namespace CVC4 {
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
   * and nested quantifier elimination.
   */
  Node rewriteInstantiation(Node q,
                            std::vector<Node>& terms,
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
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
  typedef context::CDHashMap< Node, int, NodeHashFunction> NodeIntMap;

 public:
  InstStrategyCegqi(QuantifiersEngine* qe);
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
  bool checkComplete() override;
  /** check complete for quantified formula */
  bool checkCompleteFor(Node q) override;
  /** check ownership */
  void checkOwnership(Node q) override;
  /** identify */
  std::string identify() const override { return std::string("Cegqi"); }
  /** get instantiator for quantifier */
  CegInstantiator* getInstantiator(Node q);
  /** get the virtual term substitution term cache utility */
  VtsTermCache* getVtsTermCache() const;
  /** get the BV inverter utility */
  BvInverter* getBvInverter() const;
  /** pre-register quantifier */
  void preRegisterQuantifier(Node q) override;
  // presolve
  void presolve() override;

  /**
   * Rewrite the instantiation inst of quantified formula q for terms; return
   * the result.
   *
   * We rewrite inst based on virtual term substitution and nested quantifier
   * elimination. For details, see "Solving Quantified Linear Arithmetic via
   * Counterexample-Guided Instantiation" FMSD 2017, Reynolds et al.
   */
  Node rewriteInstantiation(Node q,
                            std::vector<Node>& terms,
                            Node inst,
                            bool doVts);
  /** get the instantiation rewriter object */
  InstantiationRewriter* getInstRewriter() const;

  //------------------- interface for CegqiOutputInstStrategy
  /** Instantiate the current quantified formula forall x. Q with x -> subs. */
  bool doAddInstantiation(std::vector<Node>& subs);
  /** Add lemma lem via the output channel of this class. */
  bool addLemma(Node lem);
  //------------------- end interface for CegqiOutputInstStrategy

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
  /** whether we have added cbqi lemma */
  NodeSet d_elim_quants;
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
  /** virtual term substitution term cache for arithmetic instantiation */
  std::unique_ptr<VtsTermCache> d_vtsCache;
  /** inversion utility for BV instantiation */
  std::unique_ptr<BvInverter> d_bv_invert;
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
  /** a small constant, used as a coefficient above */
  Node d_small_const;
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

  //for identification
  uint64_t d_qid_count;
  //nested qe map
  std::map< Node, Node > d_nested_qe;
  //mark ids on quantifiers 
  Node getIdMarkedQuantNode( Node n, std::map< Node, Node >& visited );
  // id to ce quant
  std::map< Node, Node > d_id_to_ce_quant;
  std::map< Node, Node > d_ce_quant_to_id;
  //do nested quantifier elimination recursive
  Node doNestedQENode( Node q, Node ceq, Node n, std::vector< Node >& inst_terms, bool doVts );
  Node doNestedQERec( Node q, Node n, std::map< Node, Node >& visited, std::vector< Node >& inst_terms, bool doVts );
  //elimination information (for delayed elimination)
  class NestedQEInfo {
  public:
    NestedQEInfo() : d_doVts(false){}
    ~NestedQEInfo(){}
    Node d_q;
    std::vector< Node > d_inst_terms;
    bool d_doVts;
  };
  std::map< Node, NestedQEInfo > d_nested_qe_info;
  NodeIntMap d_nested_qe_waitlist_size;
  NodeIntMap d_nested_qe_waitlist_proc;
  std::map< Node, std::vector< Node > > d_nested_qe_waitlist;

  /** Do nested quantifier elimination.
   *
   * This rewrites the quantified formulas in inst based on nested quantifier
   * elimination. In this method, inst is the instantiation of quantified
   * formula q for the vector terms. The flag doVts indicates whether we must
   * apply virtual term substitution (if terms contains virtual terms).
   */
  Node doNestedQE(Node q, std::vector<Node>& terms, Node inst, bool doVts);
};


}
}
}

#endif
