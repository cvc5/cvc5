/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Relevant preregistration policy
 */

#include "cvc5_private.h"

#ifndef CVC5__DECISION__PROP_FINDER_H
#define CVC5__DECISION__PROP_FINDER_H

#include "context/cdo.h"
#include "decision/justify_cache.h"
#include "decision/justify_info.h"
#include "expr/node.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_types.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace prop {

/**
 * Information maintained for a formula for tracking relevancy.
 */
class RlvInfo
{
 public:
  RlvInfo(context::Context* c);
  /** The iteration (see updateRelevantNext) */
  context::CDO<size_t> d_iter;
  /**
   * Tracks which polarity the formula is relevant. Intuitively, a formula that
   * is relevant with polarity b is such that assigning its value to ~b
   * may contribute to SAT conflict.
   *
   * In particular d_rval is either:
   * SAT_VALUE_TRUE, SAT_VALUE_FALSE, or SAT_VALUE_UNKNOWN indicating that
   * the formula is relevant in both polarities.
   */
  context::CDO<SatValue> d_rval;
  /** The last child of this formula we processed */
  context::CDO<size_t> d_childIndex;
  /**
   * Parent list, a list of nodes that is waiting for the value of this node to
   * be assigned for the purposes of updating justification and relevance.
   */
  context::CDList<Node> d_parentList;
  /**
   * Parent list polarity, only for parents who are IMPLIES, OR, AND. This
   * stores the (implicit) polarity of this formula in the parent. For
   * example, for the RlvInfo of F, we have:
   *    d_parentListPol[ (and (not F) G) ] = false
   *    d_parentListPol[ (or F G) ] = true
   *    d_parentListPol[ (=> F G) ] = false
   */
  std::map<Node, bool> d_parentListPol;
};

/**
 * The relevant preregistration policy. This implements a policy where
 * only a subset of theory literals are preregistered at any given time.
 * This selection is based on a notion of relevance. Some simple examples
 * of the intuition:
 * - Say (or A B C) is an input formula and no literal is assigned, then we
 * preregister A only.
 * - Say (or A B C) is an input formula and A is already asserted true, then we
 * preregister nothing since this formula is already justifed.
 * - Say (and A B C) is an input formula, then we preregister A, B, C.
 * - Say (= A (and B C)) is an input formula and A is already asserted true,
 * then we preregister B and C, since assigning either B or C to false would
 * derive a conflict.
 * - Say (= A (and B C)) is an input formula and A is already asserted false,
 * then we preregister B only, since both B and C would have to be true to
 * derive a conflict.
 * - Say (ite A B C) is an input formula and A is already asserted false, then
 * we preregister C.
 *
 * The intuition in the above cases is that we want to preregister only
 * the literals that, if they were to be T-propagated, could contribute towards
 * a SAT conflict in the current context.
 *
 * More generally, this class tracks relevance on formulas in the input. All
 * top-level input formulas and lemmas are assigned relevance true. A formula
 * marked relevant may cause its children to be relevant. Any theory literal
 * marked relevant (in either polarity) is preregistered.
 */
class RelevantPreregistrar : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  RelevantPreregistrar(Env& env, CDCLTSatSolver* ss, CnfStream* cs);
  ~RelevantPreregistrar();
  /**
   * Called the beginning of theory checks (in TheoryProxy), adds literals to
   * preregister to toPreregister.
   */
  void check(std::vector<TNode>& toPreregister);
  /**
   * Notify n is an assertion (input formula), possibly associated with
   * skolem.
   */
  void addAssertion(TNode n, TNode skolem, bool isLemma);
  /** Notify that n is a literal allocated by the SAT solver */
  void notifySatLiteral(TNode n);
  /**
   * Notify active skolem definitions, adds literals to preregister to
   * toPreregister.
   */
  void notifyActiveSkolemDefs(std::vector<TNode>& defs,
                              std::vector<TNode>& toPreregister);
  /**
   * Notify that n is asserted from SAT solver, return true if we should
   * assert n to the theory engine, and adds literals to
   * preregister to toPreregister.
   */
  bool notifyAsserted(TNode n, std::vector<TNode>& toPreregister);

 private:
  /**
   * Set that n should be considered relevant, and adds literals to
   * preregister to toPreregister.
   */
  void setRelevant(TNode n, std::vector<TNode>& toPreregister);
  /**
   * Updates the state of formulas in toVisit regarding relevance, and adds
   * literals to preregister to toPreregister.
   */
  void updateRelevant(std::vector<TNode>& toVisit,
                      std::vector<TNode>& toPreregister);
  /**
   * Process the next step for handling the relevance of n. Called when n
   * is the back element of toVisit.
   *
   * This may add literals to preregister to toPreregister, or modify the list
   * of formulas to visit (toVisit), e.g. either by popping n from this vector,
   * or pushing its direct children to this vector.
   *
   * In detail, we consider the state of how n has been processed (which is
   * stored in d_pstate[n]), and whether n has already been justified (via
   * d_jcache):
   *
   * If n has already been justified, there is nothing to do, we pop n from
   * toVisit and return.
   *
   * Otherwise, this method depends on the relevance of n and its kind. The
   * following describes what is done, where this method implements
   * one step of the overall behavior:
   *
   * - If n is a conjunction/disjunction that requires all children to be a
   * certain value to be justified (e.g. AND with relevance true, OR with
   * relevance false), then we do two passes (RlvInfo::d_iter):
   *   - On the first iteration (d_iter=0), we iterate over children, marking
   *     them as relevant. If we encounter a child that is justified with a
   *     value that implies ours (e.g. a false child of AND), then we mark
   *     ourselves as justified and stop the iteration.
   *   - On the second iteration (d_iter=1), we iterate over children. If
   *     we encounter a child whose value is unknown, we mark it as watched,
   *     i.e. we stop iterating and our relevance is updated when its value is
   *     assigned. If all children have values, note these values are
   *     non-forcing, and we mark ourselves justified (i.e. an AND with all
   *     true children is justified true).
   * - If n is a conjunction/disjunction that requires one child to be a
   * certain value to be justified (e.g. AND with relevance false, OR with
   * relevance true), then:
   *    - We iterate over children, marking them as relevant. If we encounter
   *      a child that is justified with a value that implies ours, then we mark
   *      ourselves as justified and stop the iteration. If we encounter a
   *      child whose value is unknown, we mark that child as watched and stop
   *      the iteration until it has a value. If all children have values, we
   *      mark ourselves justified with the appropriate value.
   * - If n is ITE/XOR/EQUAL, then:
   *    - We mark the first child as relevant with unknown (both) polarities.
   *    - If the first child is assigned a value, then based on that value,
   *      we mark another child as relevant: if n is ITE, then the relevant
   *      branch is marked relevant; if n is XOR/EQUAL, then the right hand
   *      side is marked relevant with the appropriate polarity.
   *    - When two children have values, then we mark ourselves justified with
   *      the appropriate value.
   * - If n is a theory literal, is added to toPreregister.
   */
  SatValue updateRelevantNext(TNode n,
                              std::vector<TNode>& toPreregister,
                              std::vector<TNode>& toVisit);
  /**
   * Mark that n is relevant with polarity val. Adds n to the vector toVisit
   * if its relevance information needs to be updated.
   */
  void markRelevant(TNode n, SatValue val, std::vector<TNode>& toVisit);
  /**
   * NOTE: child should be a direct child of parent, with its negation.
   *
   * @param implJustify if not unknown, this is the polarity of child in parent
   * that would imply the value of the parent
   *
   */
  void markWatchedParent(TNode child,
                         TNode parent,
                         SatValue implJustify = SAT_VALUE_UNKNOWN);
  /**
   * Process the justification for all terms in justifyQueue, which contains
   * a list of formulas that have just been justified with the given values.
   * Add all terms that need to update their relevance to toVisit.
   */
  void updateJustify(std::vector<std::pair<TNode, SatValue>>& justifyQueue,
                     std::vector<TNode>& toVisit);
  /** get RlvInfo */
  RlvInfo* getInfo(TNode n);
  /** mk RlvInfo */
  RlvInfo* mkInfo(TNode n);
  /** mk or get RlvInfo */
  RlvInfo* getOrMkInfo(TNode n);
  /** The relevance state of each relevant formula in the input */
  context::CDInsertHashMap<Node, std::shared_ptr<RlvInfo>> d_pstate;
  /** The list of assertions */
  context::CDList<Node> d_assertions;
  /** List of preregistered literals */
  NodeSet d_preregistered;
  /** The index of the next assertion to satify */
  context::CDO<size_t> d_assertionIndex;
  /** Null node */
  TNode d_null;
  /** A justification cache */
  decision::JustifyCache d_jcache;
  /** Takes the union of the relevance values denoted by r1 and r2 */
  static SatValue relevantUnion(SatValue r1, SatValue r2);
  /** stats for debugging */
  context::CDO<size_t> d_statSatPrereg;
  context::CDO<size_t> d_statPrereg;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__DECISION__PROP_FINDER_H */
