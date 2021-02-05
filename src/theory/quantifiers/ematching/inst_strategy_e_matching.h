/*********************                                                        */
/*! \file inst_strategy_e_matching.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief E matching instantiation strategies
 **/

#include "cvc4_private.h"

#ifndef CVC4__INST_STRATEGY_E_MATCHING_H
#define CVC4__INST_STRATEGY_E_MATCHING_H

#include "theory/quantifiers/ematching/inst_strategy.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers/quant_relevance.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * This class is responsible for instantiating quantifiers based on
 * automatically generated triggers. It selects pattern terms, generates
 * and manages triggers, and uses a strategy for processing them.
 */
class InstStrategyAutoGenTriggers : public InstStrategy
{
 public:
  enum
  {
    RELEVANCE_NONE,
    RELEVANCE_DEFAULT,
  };

 private:
  /** trigger generation strategy */
  options::TriggerSelMode d_tr_strategy;
  /** regeneration */
  bool d_regenerate;
  int d_regenerate_frequency;
  /** (single,multi) triggers for each quantifier */
  std::map<Node, std::map<inst::Trigger*, bool> > d_auto_gen_trigger[2];
  std::map<Node, int> d_counter;
  /** single, multi triggers for each quantifier */
  std::map<Node, std::vector<Node> > d_patTerms[2];
  std::map<Node, std::map<Node, bool> > d_patReqPol;
  /** information about triggers */
  std::map<Node, bool> d_is_single_trigger;
  std::map<Node, bool> d_single_trigger_gen;
  std::map<Node, bool> d_made_multi_trigger;
  // processed trigger this round
  std::map<Node, std::map<inst::Trigger*, bool> > d_processed_trigger;
  // instantiation no patterns
  std::map<Node, std::vector<Node> > d_user_no_gen;
  // number of trigger variables per quantifier
  std::map<Node, unsigned> d_num_trigger_vars;
  std::map<Node, Node> d_vc_partition[2];
  std::map<Node, Node> d_pat_to_mpat;

 private:
  /** process functions */
  void processResetInstantiationRound(Theory::Effort effort) override;
  /** Process */
  InstStrategyStatus process(Node q, Theory::Effort effort, int e) override;
  /**
   * Generate triggers for quantified formula q.
   */
  void generateTriggers(Node q);
  /**
   * Generate pattern terms for quantified formula q.
   */
  bool generatePatternTerms(Node q);
  void addPatternToPool(Node q, Node pat, unsigned num_fv, Node mpat);
  void addTrigger(inst::Trigger* tr, Node f);
  /** has user patterns */
  bool hasUserPatterns(Node q);
  /** has user patterns */
  std::map<Node, bool> d_hasUserPatterns;

 public:
  InstStrategyAutoGenTriggers(QuantifiersEngine* qe,
                              QuantifiersState& qs,
                              QuantRelevance* qr);
  ~InstStrategyAutoGenTriggers() {}

  /** get auto-generated trigger */
  inst::Trigger* getAutoGenTrigger(Node q);
  /** identify */
  std::string identify() const override
  {
    return std::string("AutoGenTriggers");
  }
  /** add pattern */
  void addUserNoPattern(Node q, Node pat);

 private:
  /**
   * Pointer to the module that computes relevance of quantifiers, which is
   * owned by the instantiation engine that owns this class.
   */
  QuantRelevance* d_quant_rel;
}; /* class InstStrategyAutoGenTriggers */
}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif
