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
    strat_uf_card,
    strat_cegqi_quant,
    strat_fmf,
    strat_last
  };
  DecisionManager(context::Context* satContext);
  ~DecisionManager() {}
  /**
   * Registers the strategy ds with this manager.
   */
  void registerStrategy(StrategyId id, DecisionStrategy* ds);
  /**
   * Initializes the strategy.
   *
   */
  void initialize();
  /** Get the next decision request */
  Node getNextDecisionRequest();

 private:
  std::map<StrategyId, std::vector<DecisionStrategy*> > d_reg_strategy;
  std::vector<DecisionStrategy*> d_strategy;
  context::CDO<unsigned> d_curr_strategy;
};

}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__DECISION_MANAGER__H */
