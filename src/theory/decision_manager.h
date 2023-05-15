/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Decision manager, which manages all decision strategies owned by
 * theory solvers within TheoryEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__DECISION_MANAGER__H
#define CVC5__THEORY__DECISION_MANAGER__H

#include <map>
#include "context/cdlist.h"
#include "theory/decision_strategy.h"

namespace cvc5::internal {
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
  typedef context::CDList<DecisionStrategy*> DecisionStrategyList;

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
  /** The scope of a strategy, used in registerStrategy below */
  enum StrategyScope
  {
    // The strategy is user-context dependent, that is, it is cleared when
    // the user context is popped.
    STRAT_SCOPE_USER_CTX_DEPENDENT,
    // The strategy is local to a check-sat call, that is, it is cleared on
    // a call to presolve.
    STRAT_SCOPE_LOCAL_SOLVE,
    // The strategy is context-independent.
    STRAT_SCOPE_CTX_INDEPENDENT,
  };
  DecisionManager(context::Context* userContext);
  ~DecisionManager() {}
  /** presolve
   *
   * This clears all decision strategies that are registered to this manager
   * that no longer exist in the current user context.
   * We require that each satisfiability check beyond the first calls this
   * function exactly once. It is called during TheoryEngine::presolve.
   */
  void presolve();
  /**
   * Registers the strategy ds with this manager. The id specifies when the
   * strategy should be run. The argument sscope indicates the scope of the
   * strategy, i.e. how long it persists.
   *
   * Typically, strategies that are user-context-dependent are those that are
   * in response to an assertion (e.g. a strategy that decides that a sygus
   * conjecture is feasible). An example of a strategy that is context
   * independent is the combined cardinality decision strategy for finite model
   * finding for UF, which is not specific to any formula/type.
   */
  void registerStrategy(StrategyId id,
                        DecisionStrategy* ds,
                        StrategyScope sscope = STRAT_SCOPE_USER_CTX_DEPENDENT);
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
  /** Set of decision strategies in this user context */
  DecisionStrategyList d_strategyCacheC;
  /** Set of decision strategies that are context independent */
  std::unordered_set<DecisionStrategy*> d_strategyCache;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__DECISION_MANAGER__H */
