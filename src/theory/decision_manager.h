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
 ** \brief Decision manager, which manages all decision strategies owned by
 ** theory solvers within TheoryEngine.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DECISION_MANAGER__H
#define __CVC4__THEORY__DECISION_MANAGER__H

#include <map>
#include "theory/decision_strategy.h"

namespace CVC4 {
namespace theory {

/** DecisionManager
 *
 * This class manages all "decision strategies" for theory solvers in
 * TheoryEngine. A decision strategy is a callback in the SAT solver for
 * imposing its next decision. This is useful, for instance, in
 * branch-and-bound algorithms where we require that the first decision
 * is a bound on some quantity. For instance, finite model finding may impose
 * a bound on the cardinality of an uninterpreted sort as the first decision.
 *
 * This class maintains a user-context-dependent set of pointers to
 * DecisionStrategy objects, which implement indivdual decision strategies.
 *
 * Decision strategies may be registered to this class via registerStrategy
 * at any time during solving. They are cleared via a call to reset during
 * TheoryEngine's postSolve method.
 *
 * Decision strategies have a fixed order, which is managed by the enumeration
 * type StrategyId, where strategies with smaller id have higher precedence
 * in our global decision strategy.
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
    STRAT_QUANT_CEGQI_FEASIBLE,
    STRAT_QUANT_SYGUS_FEASIBLE,
    STRAT_QUANT_SYGUS_STREAM_FEASIBLE,
    // placeholder for last model-sound required strategy
    STRAT_LAST_M_SOUND,

    //----- finite model finding strategies
    //  We require these go here for the sake of finite-model completeness. In
    //  other words, if these strategies did not go before other decisions, we
    //  might be non-terminating instead of answering "sat" with a solution
    //  within a given a bound.
    STRAT_UF_COMBINED_CARD,
    STRAT_UF_CARD,
    STRAT_DT_SYGUS_ENUM_ACTIVE,
    STRAT_DT_SYGUS_ENUM_SIZE,
    STRAT_STRINGS_SUM_LENGTHS,
    STRAT_QUANT_BOUND_INT_SIZE,
    STRAT_QUANT_CEGIS_UNIF_NUM_ENUMS,
    STRAT_SEP_NEG_GUARD,
    // placeholder for last finite-model-complete required strategy
    STRAT_LAST_FM_COMPLETE,

    //----- decision strategies that are optimizations
    STRAT_ARRAYS,

    STRAT_LAST
  };
  DecisionManager(context::Context* satContext);
  ~DecisionManager() {}
  /** reset the strategy
   *
   * This clears all decision strategies that are registered to this manager.
   * We require that each satisfiability check beyond the first calls this
   * function exactly once. Currently, it is called during
   * TheoryEngine::postSolve.
   */
  void reset();
  /**
   * Registers the strategy ds with this manager. The id specifies when the
   * strategy should be run.
   */
  void registerStrategy(StrategyId id, DecisionStrategy* ds);
  /** Get the next decision request
   *
   * If this method returns a non-null node n, then n is a literal corresponding
   * to the next decision that the SAT solver should take. If this method
   * returns null, then no decisions are required by a decision strategy
   * registered to this class. In the latter case, the SAT solver will choose
   * a decision based on its given heuristic.
   */
  Node getNextDecisionRequest();

 private:
  /** Map containing all strategies registered to this manager */
  std::map<StrategyId, std::vector<DecisionStrategy*> > d_reg_strategy;
};

}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__DECISION_MANAGER__H */
