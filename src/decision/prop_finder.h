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
  /** The relevant value */
  context::CDO<prop::SatValue> d_rval;
  /** The justified value */
  context::CDO<prop::SatValue> d_jval;
  /** The last child we looked up */
  context::CDO<size_t> d_childIndex;
  /** 
   * Parent list, the node we are a child of, the second in pair is our
   * polarity, e.g. false means we are a negated child.
   */
  context::CDList<std::pair<Node, bool>> d_parentList;
  /** Has justified */
  bool hasJustified() const;
};

/**
 */
class PropFinder : protected EnvObj
{
 public:
  PropFinder(Env& env, prop::CDCLTSatSolverInterface* ss, prop::CnfStream* cs);
  ~PropFinder();
  /** Notify assertion */
  void addAssertion(TNode n,
                    TNode skolem,
                    bool isLemma,
                    std::vector<TNode>& toPreregister);
  /** Notify active skolem definitions */
  void notifyActiveSkolemDefs(std::vector<TNode>& defs,
                              std::vector<TNode>& toPreregister);
  /** Notify that n is asserted from SAT solver */
  void notifyAsserted(TNode n, std::vector<TNode>& toPreregister);

 private:
  /** Set relevant */
  void updateRelevant(TNode n, std::vector<TNode>& toPreregister);
  void updateRelevantInternal(TNode n,
                              prop::SatValue val,
                              std::vector<TNode>& toPreregister);
  void notifyParentInternal(TNode n, bool childVal);
  /** mk or get PropFindInfo */
  PropFindInfo* getInfo(TNode n);
  /** mk or get PropFindInfo */
  PropFindInfo* mkInfo(TNode n);
  /** mk or get PropFindInfo */
  PropFindInfo* getOrMkInfo(TNode n);
  /** The state */
  context::CDInsertHashMap<Node, std::shared_ptr<PropFindInfo> > d_pstate;
  /** Null node */
  TNode d_null;
  /** A justification cache */
  JustifyCache d_jcache;
  /** */
  static prop::SatValue relevantUnion(prop::SatValue r1, prop::SatValue r2);
};

}  // namespace decision
}  // namespace cvc5::internal

#endif /* CVC5__DECISION__PROP_FINDER_H */
