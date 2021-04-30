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
 * It also maintains a dynamic list of assertions, called skolem definitions,
 * that correspond to definitions of the behavior of skolems that occur in
 * assertions.
 *
 * As an example, say our input formulas are:
 *   (or (and A B) C D), (or E F)
 * where A, B, C, D, E, F are theory literals. Moreover, say we are in a
 * state where the SAT solver has assigned values:
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
 * After deciding C, the solver may backtrack, or otherwise end up in a state
 * where we have assigned:
 *   { A -> false, E -> true, C -> true }
 * In the next call to getNext, this module will realize that the input
 * is already true, and hence it will return the null SAT decision literal,
 * indicating that no further decisions are necessary.
 *
 * One novel feature of this module is that it maintains a SAT-context-dependent
 * stack corresponding to the current path in the input formula we are trying
 * to satisfy. This means that computing the next decision does not require
 * traversing the current assertion.
 */
class JustificationStrategy
{
 public:
  /** Constructor */
  JustificationStrategy(context::Context* c,
                        context::UserContext* u,
                        prop::SkolemDefManager* skdm);

  /** Finish initialize */
  void finishInit(prop::CDCLTSatSolverInterface* ss, prop::CnfStream* cs);

  /** Presolve, called at the beginning of each check-sat call */
  void presolve();

  /**
   * Gets the next decision based on the current assertion to satisfy. This
   * returns undefSatLiteral if there are no more assertions. In this case,
   * all relevant input assertions are already propositionally satisfied by
   * the current assignment.
   * 
   * @return The next SAT literal to decide on.
   */
  prop::SatLiteral getNext();

  /** 
   * Are we finished assigning values to literals?
   * 
   * @return true if and only if all relevant input assertions are already
   * propositionally satisfied by the current assignment.
   */
  bool isDone();

  /**
   * Notify this class that assertion is an (input) assertion, not corresponding
   * to a skolem definition.
   */
  void addAssertion(TNode assertion);
  /**
   * Notify this class that lem is the skolem definition for skolem, which is
   * a part of the current assertions.
   */
  void addSkolemDefinition(TNode lem, TNode skolem);
  /**
   * Notify this class that literal n has been asserted. This is triggered when
   * n is sent to TheoryEngine. This activates skolem definitions for skolems
   * k that occur in n.
   */
  void notifyAsserted(TNode n);

 private:
  /**
   * Helper method to insert assertions in `toProcess` to `d_assertions` or
   * `d_skolemAssertions` based on `useSkolemList`.
   */
  void insertToAssertionList(std::vector<TNode>& toProcess, bool useSkolemList);
  /** 
   * Refresh current assertion. This ensures that d_stack has a current
   * assertionto satisfy. If does not already have one, we take the next
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
   * @param lastChildVal The value determined for the last child of the node of ji.
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
  /** Pointer to the SAT context */
  context::Context* d_context;
  /** Pointer to the CNF stream */
  prop::CnfStream* d_cnfStream;
  /** Pointer to the SAT solver */
  prop::CDCLTSatSolverInterface* d_satSolver;
  /** Pointer to the skolem definition manager */
  prop::SkolemDefManager* d_skdm;
  /** The assertions, which are user-context dependent. */
  AssertionList d_assertions;
  /** The skolem assertions */
  AssertionList d_skolemAssertions;

  /** Mapping from non-negated nodes to their SAT value */
  context::CDInsertHashMap<Node, prop::SatValue, NodeHashFunction> d_justified;
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
