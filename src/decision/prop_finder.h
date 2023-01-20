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
namespace decision {

class PropFindInfo
{
 public:
  PropFindInfo(context::Context* c);
  /** The iteration */
  context::CDO<size_t> d_iter;
  /** The relevant value */
  context::CDO<prop::SatValue> d_rval;
  /** The last child we looked up */
  context::CDO<size_t> d_childIndex;
  /**
   * Parent list, a list of nodes that is waiting for the value of this node to
   * be assigned for the purposes of updating relevance.
   */
  context::CDList<Node> d_parentList;
  /** Parent list polarity */
  std::map<Node, bool> d_parentListPol;
  /** set finished */
  void setInactive();
  /** is finished */
  bool isActive() const;
};

/**
 */
class PropFinder : protected EnvObj
{
 public:
  PropFinder(Env& env, prop::CDCLTSatSolverInterface* ss, prop::CnfStream* cs);
  ~PropFinder();
  /** theory check */
  void check(std::vector<TNode>& toPreregister);
  /** Notify assertion */
  void addAssertion(TNode n, TNode skolem, bool isLemma);
  void notifyPreRegister(TNode n);
  /** Notify active skolem definitions */
  void notifyActiveSkolemDefs(std::vector<TNode>& defs,
                              std::vector<TNode>& toPreregister);
  /** Notify that n is asserted from SAT solver */
  void notifyAsserted(TNode n, std::vector<TNode>& toPreregister);

 private:
  /** Set relevant */
  void updateRelevant(TNode n, std::vector<TNode>& toPreregister);
  void updateRelevantInternal(std::vector<TNode>& toVisit,
                              std::vector<TNode>& toPreregister);
  prop::SatValue updateRelevantInternal2(TNode n,
                                         std::vector<TNode>& toPreregister,
                                         std::vector<TNode>& toVisit);
  void markRelevant(TNode n, prop::SatValue val, std::vector<TNode>& toVisit);
  /**
   * NOTE: child should be a direct child of parent, with its negation.
   */
  void markWatchedParent(TNode child, TNode parent);
  void getWatchParents(TNode n, std::vector<TNode>& toVisit);
  /** mk or get PropFindInfo */
  PropFindInfo* getInfo(TNode n);
  /** mk or get PropFindInfo */
  PropFindInfo* mkInfo(TNode n);
  /** mk or get PropFindInfo */
  PropFindInfo* getOrMkInfo(TNode n);
  /** The state */
  context::CDInsertHashMap<Node, std::shared_ptr<PropFindInfo>> d_pstate;
  /** The list of assertions */
  context::CDList<Node> d_assertions;
  /** The index of the next assertion to satify */
  context::CDO<size_t> d_assertionIndex;
  /** Null node */
  TNode d_null;
  /** A justification cache */
  JustifyCache d_jcache;
  /** */
  static prop::SatValue relevantUnion(prop::SatValue r1, prop::SatValue r2);
  /** stats */
  context::CDO<size_t> d_statSatPrereg;
  context::CDO<size_t> d_statPrereg;
};

}  // namespace decision
}  // namespace cvc5::internal

#endif /* CVC5__DECISION__PROP_FINDER_H */
