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
 */
class RelevantPreregistrar : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  RelevantPreregistrar(Env& env, CDCLTSatSolverInterface* ss, CnfStream* cs);
  ~RelevantPreregistrar();
  /** theory check */
  void check(std::vector<TNode>& toPreregister);
  /** Notify assertion */
  void addAssertion(TNode n, TNode skolem, bool isLemma);
  /** Notify that n is a literal allocated by the SAT solver */
  void notifySatLiteral(TNode n);
  /** Notify active skolem definitions */
  void notifyActiveSkolemDefs(std::vector<TNode>& defs,
                              std::vector<TNode>& toPreregister);
  /**
   * Notify that n is asserted from SAT solver, return true if we should
   * assert n to the theory engine.
   */
  bool notifyAsserted(TNode n, std::vector<TNode>& toPreregister);

  void debugCheck();

 private:
  /** Set relevant */
  void updateRelevant(TNode n, std::vector<TNode>& toPreregister);
  void updateRelevantInternal(std::vector<TNode>& toVisit,
                              std::vector<TNode>& toPreregister);
  SatValue updateRelevantInternal2(TNode n,
                                   std::vector<TNode>& toPreregister,
                                   std::vector<TNode>& toVisit);
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

  void debugCheckAssertion(const Node& a);
  /** mk or get RlvInfo */
  RlvInfo* getInfo(TNode n);
  /** mk or get RlvInfo */
  RlvInfo* mkInfo(TNode n);
  /** mk or get RlvInfo */
  RlvInfo* getOrMkInfo(TNode n);
  /** The state */
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
  /** */
  static SatValue relevantUnion(SatValue r1, SatValue r2);
  /** stats */
  context::CDO<size_t> d_statSatPrereg;
  context::CDO<size_t> d_statPrereg;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__DECISION__PROP_FINDER_H */
