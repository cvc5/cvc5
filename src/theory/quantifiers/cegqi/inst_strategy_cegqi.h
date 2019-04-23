/*********************                                                        */
/*! \file inst_strategy_cegqi.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief counterexample-guided quantifier instantiation
 **/


#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INST_STRATEGY_CEGQI_H
#define __CVC4__THEORY__QUANTIFIERS__INST_STRATEGY_CEGQI_H

#include "theory/decision_manager.h"
#include "theory/quantifiers/cegqi/ceg_instantiator.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class InstStrategyCegqi;

/**
 * An output channel class, used by instantiator objects below. The methods
 * of this class call the corresponding functions of InstStrategyCegqi below.
 */
class CegqiOutputInstStrategy : public CegqiOutput
{
 public:
  CegqiOutputInstStrategy(InstStrategyCegqi* out) : d_out(out) {}
  /** The module whose functions we call. */
  InstStrategyCegqi* d_out;
  /** add instantiation */
  bool doAddInstantiation(std::vector<Node>& subs) override;
  /** is eligible for instantiation */
  bool isEligibleForInstantiation(Node n) override;
  /** add lemma */
  bool addLemma(Node lem) override;
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
  /** pre-register quantifier */
  void preRegisterQuantifier(Node q) override;
  // presolve
  void presolve() override;
  /** Do nested quantifier elimination. */
  Node doNestedQE(Node q, std::vector<Node>& inst_terms, Node lem, bool doVts);

  //------------------- interface for CegqiOutputInstStrategy
  /** Instantiate the current quantified formula forall x. Q with x -> subs. */
  bool doAddInstantiation(std::vector<Node>& subs);
  /**
   * Are we allowed to instantiate the current quantified formula with n? This
   * includes restrictions such as if n is a variable, it must occur free in
   * the current quantified formula.
   */
  bool isEligibleForInstantiation(Node n);
  /** Add lemma lem via the output channel of this class. */
  bool addLemma(Node lem);
  //------------------- end interface for CegqiOutputInstStrategy

 protected:
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
   * An output channel used by instantiators for communicating with this
   * class.
   */
  std::unique_ptr<CegqiOutputInstStrategy> d_out;
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

};


}
}
}

#endif
