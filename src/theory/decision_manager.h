/*********************                                                        */
/*! \file decision_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief decision_manager
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DECISION_MANAGER__H
#define __CVC4__THEORY__DECISION_MANAGER__H

#include <map>
#include "context/cdo.h"
#include "expr/node.h"
#include "theory/valuation.h"

namespace CVC4 {
namespace theory {

/**
 * Virtual base class for decision strategies.
 */
class DecisionStrategy
{
 public:
  DecisionStrategy() {}
  virtual ~DecisionStrategy() {}
  virtual void initialize() = 0;
  virtual Node getNextDecisionRequest() = 0;
  virtual std::string identify() const = 0;
};

/**
 * Decision strategy finite model finding.
 *
 * This is a virtual base class for decision strategies that follow the
 * "finite model finding" pattern for decisions. Such strategies have the
 * distinguishing feature that they are interested in a stream of literals
 * L_1, L_2, L_3, ... and so on. At any given time, they request that L_i is
 * asserted true for a minimal i.
 *
 * To enforce this strategy, this class maintains a SAT-context dependent
 * index d_curr_literal, which corresponds to the
 */
class DecisionStrategyFmf : public DecisionStrategy
{
 public:
  DecisionStrategyFmf(context::Context* satContext, Valuation valuation);
  virtual ~DecisionStrategyFmf() {}
  /** initialize */
  void initialize() override;
  /** get next decision request */
  Node getNextDecisionRequest() override;
  /** are we currently ready to make the decision? */
  virtual bool isReadyForDecision();
  /** Make the n^th literal of this strategy */
  virtual Node mkLiteral(unsigned n) = 0;
  /**
   * This method returns true iff there exists a (minimal) i such that L_i
   * is a literal allocated by this class, and is asserted true in the current
   * context. If it returns true, the argument i is set to this i.
   */
  bool getAssertedLiteralIndex(unsigned& i);
  /**
   * This method returns the literal L_i allocated by this class that
   * has been asserted true in the current context and is such that i is
   * minimal. It returns null if no such literals exist.
   */
  Node getAssertedLiteral();
  /** Get the n^th literal of this strategy */
  Node getLiteral(unsigned lit);

 private:
  /**
   * The valuation of this class, used for knowing what literals are asserted,
   * and with what polarity.
   */
  Valuation d_valuation;
  /**
   * The (SAT-context-dependent) flag that is true if there exists a literal
   * of this class that is asserted true in the current context, according to
   * d_valuation.
   */
  context::CDO<bool> d_has_curr_literal;
  /**
   * The (SAT-context-dependent) index of the current literal of this strategy.
   * This corresponds to the first literal that is not asserted false in the
   * current context, according to d_valuation.
   */
  context::CDO<unsigned> d_curr_literal;
  /** the list of literals of this strategy */
  std::vector<Node> d_literals;
};

/** 
 * Special case of above where we only wish to allocate a single literal L_1.
 */
class DecisionStrategySingleton : public DecisionStrategyFmf
{
public:
  DecisionStrategySingleton(context::Context* satContext, Valuation valuation);
  /** 
   * Make the n^th literal of this strategy. This method returns mkLiteral if n=0, null otherwise.
   */
  Node mkLiteral(unsigned n) override;
  /** Make the literal of this strategy */
  virtual Node mkSingleLiteral() = 0;
  /** Get single literal */
  Node getSingleLiteral();
};

/** DecisionManager
 *
 */
class DecisionManager
{
 public:
  enum StrategyId
  {
    // The order of the global decision strategy used by the TheoryEngine
    // for getNextDecision.

    //----- assume-feasibile strategies
    //  These are required to go first for the sake of model-soundness. In
    //  other words, if these strategies did not go first, we might answer
    //  "sat" for problems that are unsat.
    strat_quant_cegqi_feasible,
    strat_quant_sygus_feasible,
    strat_last_m_sound,

    //----- finite model finding strategies
    //  We require these go here for the sake of finite-model completeness. In
    //  other words, if these strategies did not go before other decisions, we
    //  might be non-terminating instead of answering "sat" with a solution
    //  within a given a bound.
    strat_uf_combined_card,
    strat_uf_card,
    strat_datatypes_sygus_enum_not_exhaust,
    strat_datatypes_sygus_enum_size,
    strat_quant_bound_int_size,
    strat_quant_cegis_unif_num_enums,
    strat_strings_sum_lengths,
    strat_sep_neg_guard,
    strat_last_fm_complete,

    //----- decision strategies that are optimizations
    strat_arrays,

    strat_last
  };
  DecisionManager(context::Context* satContext);
  ~DecisionManager() {}
  /**
   * Registers the strategy ds with this manager.
   */
  void registerStrategy(StrategyId id, DecisionStrategy* ds, bool append=true);
  /**
   * Initializes the strategy.
   */
  //void initialize();
  /** Get the next decision request */
  Node getNextDecisionRequest(unsigned& priorty);

 private:
  std::map<StrategyId, std::vector<DecisionStrategy*> > d_reg_strategy;
  //std::vector<DecisionStrategy*> d_strategy;
  //context::CDO<unsigned> d_curr_strategy;
};

}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__DECISION_MANAGER__H */
