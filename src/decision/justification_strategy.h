/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the justification SAT decision strategy
 */

#include "cvc5_private.h"

#ifndef CVC5__DECISION__JUSTIFICATION_STRATEGY_H
#define CVC5__DECISION__JUSTIFICATION_STRATEGY_H

#include "context/cdinsert_hashmap.h"
#include "context/cdo.h"
#include "decision/assertion_list.h"
#include "decision/decision_engine.h"
#include "decision/justify_info.h"
#include "decision/justify_stack.h"
#include "decision/justify_stats.h"
#include "expr/node.h"
#include "options/decision_options.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_types.h"

namespace cvc5 {

namespace prop {
class SkolemDefManager;
}

namespace decision {

/**
 * An implementation of justification SAT decision heuristic. This class
 * is given access to the set of input formulas, and chooses next decisions
 * based on the structure of the input formula.
 *
 * Notice that the SAT solver still propagates values for literals in the
 * normal way based on BCP when using this SAT decision heuristic. This means
 * that values for literals can be assigned between calls to get next
 * decision. Thus, this module has access to the SAT solver for the purpose
 * of looking up values already assigned to literals.
 *
 * One novel feature of this module is that it maintains a SAT-context-dependent
 * stack corresponding to the current path in the input formula we are trying
 * to satisfy. This means that computing the next decision does not require
 * traversing the current assertion.
 *
 * As an example, say our input formulas are:
 *   (or (and A B) C D), (or E F)
 * where A, B, C, D, E, F are theory literals. Moreover, say we are in a
 * state where the SAT solver has initially assigned values:
 *   { A -> false, E -> true }
 * Given a call to getNext, this module will analyze what is the next
 * literal that would contribute towards making the input formulas evaluate to
 * true. Assuming it works on assertions and terms left-to-right, it will
 * perform the following reasoning:
 * - The desired value of (or (and A B) C D) is true
 *   - The desired value of (and A B) is true
 *     - The desired value of A is true,
 *       ...The value of A was assigned false
 *     ...The value of (and A B) is false
 *   - Moving to the next literal, the desired value of C is true
 *     ...The value of C is unassigned, return C as a decision.
 * After deciding C, assuming no backtracking occurs, we end up in a state
 * where we have assigned:
 *   { A -> false, E -> true, C -> true }
 * In the next call to getNext, this module will proceed, keeping the stack
 * from the previous call:
 *     ... The value of C is true
 *   ... The value of (or (and A B) C D) is true
 * - Moving to the next assertion, the desired value of (or E F) is true
 *   - The desired value of E is true
 *     ... The value of E is (already) assigned true
 *   ... the value of (or E F) is true.
 * - The are no further assertions.
 * Hence it will return the null SAT decision literal, indicating that no
 * further decisions are necessary to satisfy the input assertions.
 *
 * This class has special handling of "skolem definitions", which arise when
 * lemmas are introduced that correspond to the behavior of skolems. As an
 * example, say our input, prior to preprocessing, is:
 *   (or (P (ite A 1 2)) Q)
 * where P is an uninterpreted predicate of type Int -> Bool. After
 * preprocessing, in particular term formula removal which replaces term-level
 * ITE terms with fresh skolems, we get this set of assertions:
 *   (or (P k) Q), (ite A (= k 1) (= k 2))
 * The second assertion is the skolem definition for k. Conceptually, this
 * lemma is only relevant if we have asserted a literal that contains k.
 * This module thus maintains two separate assertion lists, one for
 * input assertions, and one for skolem definitions. The latter is populated
 * only as skolems appear in assertions. In this example, we have initially:
 *   input assertions = { (or (P k) Q) }
 *   relevant skolem definitions =  {}
 *   SAT context = {}
 * Say this module returns (P k) as a decision. When this is asserted to
 * the theory engine, a call to notifyAsserted is made with (P k). The
 * skolem definition manager will recognize that (P k) contains k and hence
 * its skolem definition is activated, giving us this state:
 *   input assertions = { (or (P k) Q) }
 *   relevant skolem definitions =  { (ite A (= k 1) (= k 2)) }
 *   SAT context = { (P k) }
 * We then proceed by satisfying (ite A (= k 1) (= k 2)), e.g. by returning
 * A as a decision for getNext.
 *
 * Notice that the above policy allows us to ignore certain skolem definitions
 * entirely. For example, if Q were to have been asserted instead of (P k),
 * then (ite A (= k 1) (= k 2)) would not be added as a relevant skolem
 * definition, and Q alone would have sufficed to show the input formula
 * was satisfied.
 */
class JustificationStrategy : public DecisionEngine
{
 public:
  /** Constructor */
  JustificationStrategy(context::Context* c,
                        context::UserContext* u,
                        prop::SkolemDefManager* skdm,
                        ResourceManager* rm);

  /** Presolve, called at the beginning of each check-sat call */
  void presolve() override;

  /**
   * Gets the next decision based on the current assertion to satisfy. This
   * returns undefSatLiteral if there are no more assertions. In this case,
   * all relevant input assertions are already propositionally satisfied by
   * the current assignment.
   *
   * @param stopSearch Set to true if we can stop the search
   * @return The next SAT literal to decide on.
   */
  prop::SatLiteral getNextInternal(bool& stopSearch) override;

  /**
   * Are we finished assigning values to literals?
   *
   * @return true if and only if all relevant input assertions are already
   * propositionally satisfied by the current assignment.
   */
  bool isDone() override;

  /**
   * Notify this class that assertion is an (input) assertion, not corresponding
   * to a skolem definition.
   */
  void addAssertion(TNode assertion) override;
  /**
   * Notify this class that lem is the skolem definition for skolem, which is
   * a part of the current assertions.
   */
  void addSkolemDefinition(TNode lem, TNode skolem) override;
  /**
   * Notify this class that literal n has been asserted. This is triggered when
   * n is sent to TheoryEngine. This activates skolem definitions for skolems
   * k that occur in n.
   */
  void notifyAsserted(TNode n) override;

 private:
  /**
   * Helper method to insert assertions in `toProcess` to `d_assertions` or
   * `d_skolemAssertions` based on `useSkolemList`.
   */
  void insertToAssertionList(std::vector<TNode>& toProcess, bool useSkolemList);
  /**
   * Refresh current assertion. This ensures that d_stack has a current
   * assertion to satisfy. If it does not already have one, we take the next
   * assertion from the list of input assertions, or from the relevant
   * skolem definitions based on the JutificationSkolemMode mode.
   *
   * @return true if we successfully initialized d_stack with the next
   * assertion to satisfy.
   */
  bool refreshCurrentAssertion();
  /**
   * Implements the above function for the case where d_stack must get a new
   * assertion to satisfy.
   *
   * @param useSkolemList If this is true, we pull the next assertion from
   * the list of relevant skolem definitions.
   * @return true if we successfully initialized d_stack with the next
   * assertion to satisfy.
   */
  bool refreshCurrentAssertionFromList(bool useSkolemList);
  /**
   * Let n be the node referenced by ji.
   *
   * This method is called either when we have yet to process any children of n,
   * or we just determined that the last child we processed of n had value
   * lastChildVal.
   *
   * Note that knowing which child of n we processed last is the value of
   * ji->d_childIndex.
   *
   * @param ji The justify node to process
   * @param lastChildVal The value determined for the last child of the node of
   * ji.
   * @return Either (1) the justify node corresponding to the next child of n to
   * consider adding to the stack, and its desired polarity, or
   * (2) a null justify node and updates lastChildVal to the value of n.
   */
  JustifyNode getNextJustifyNode(JustifyInfo* ji, prop::SatValue& lastChildVal);
  /**
   * Returns the value TRUE/FALSE for n, or UNKNOWN otherwise.
   *
   * We return a value for n only if we have justified its values based on its
   * children. For example, we return UNKNOWN for n of the form (and A B) if
   * A and B have UNKNOWN value, even if the SAT solver has assigned a value for
   * (internal) node n. If n itself is a theory literal, we lookup its value
   * in the SAT solver if it is not already cached.
   */
  prop::SatValue lookupValue(TNode n);
  /** Is n a theory literal? */
  static bool isTheoryLiteral(TNode n);
  /** Is n a theory atom? */
  static bool isTheoryAtom(TNode n);
  /** Pointer to the skolem definition manager */
  prop::SkolemDefManager* d_skdm;
  /** The assertions, which are user-context dependent. */
  AssertionList d_assertions;
  /** The skolem assertions */
  AssertionList d_skolemAssertions;

  /** Mapping from non-negated nodes to their SAT value */
  context::CDInsertHashMap<Node, prop::SatValue> d_justified;
  /** A justify stack */
  JustifyStack d_stack;
  /** The last decision literal */
  context::CDO<TNode> d_lastDecisionLit;
  //------------------------------------ activity
  /** Current assertion we are checking for status (context-independent) */
  Node d_currUnderStatus;
  /** Whether we have added a decision while considering d_currUnderStatus */
  bool d_currStatusDec;
  //------------------------------------ options
  /** using relevancy order */
  bool d_useRlvOrder;
  /** using stop only */
  bool d_decisionStopOnly;
  /** skolem mode */
  options::JutificationSkolemMode d_jhSkMode;
  /** skolem relevancy mode */
  options::JutificationSkolemRlvMode d_jhSkRlvMode;
  /** The statistics */
  JustifyStatistics d_stats;
};

}  // namespace decision
}  // namespace cvc5

#endif /* CVC5__DECISION__JUSTIFICATION_STRATEGY_H */
