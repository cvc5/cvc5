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
 * Propagation finder
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
  /** The iteration */
  context::CDO<size_t> d_iter;
  /** The relevant value */
  context::CDO<SatValue> d_rval;
  /** The last child we looked up */
  context::CDO<size_t> d_childIndex;
  /**
   * Parent list, a list of nodes that is waiting for the value of this node to
   * be assigned for the purposes of updating relevance.
   */
  context::CDList<Node> d_parentList;
  /**
   * Parent list polarity, only for parents who are IMPLIES, OR, AND.
   */
  std::map<Node, bool> d_parentListPol;
  /** set finished */
  void setInactive();
  /** is finished */
  bool isActive() const;
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
 * then we preregister B, C.
 * - Say (= A (and B C)) is an input formula and A is already asserted false,
 * then we preregister B only.
 * - Say (ite A B C) is an input formula and A is already asserted false, then
 * we preregister C.
 * 
 * The intuition in the above cases is that we want to preregister only
 * the literals that, if they were to be T-propagated, could contribute towards
 * a SAT conflict in the current context.
 */
class RelevantPreregistrar : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  RelevantPreregistrar(Env& env, CDCLTSatSolverInterface* ss, CnfStream* cs);
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
   * Update that n should be considered relevant, and adds literals to
   * preregister to toPreregister.
   */
  void updateRelevant(TNode n, std::vector<TNode>& toPreregister);
  /**
   * Update that n should be considered relevant, and adds literals to
   * preregister to toPreregister.
   */
  void updateRelevantInternal(std::vector<TNode>& toVisit,
                              std::vector<TNode>& toPreregister);
  SatValue updateRelevantInternal2(TNode n,
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
   * Process the justification for all terms in justifyQueue, add all terms
   * that need to update their relevance to toVisit.
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
