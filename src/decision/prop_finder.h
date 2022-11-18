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
  /** This node */
  Node d_node;
  /** The last child we looked up */
  context::CDO<size_t> d_childIndex;
  /** Parent list */
  context::CDList<PropFindInfo*> d_parentList;
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
  void setRelevant(TNode n, std::vector<TNode>& toPreregister);
  /** mk or get PropFindInfo */
  PropFindInfo* getOrMkInfo(TNode n);
  /** The state */
  context::CDInsertHashMap<Node, std::shared_ptr<PropFindInfo> > d_pstate;
  /** Null node */
  TNode d_null;
  /** A justification cache */
  JustifyCache d_jcache;
};

}  // namespace decision
}  // namespace cvc5::internal

#endif /* CVC5__DECISION__PROP_FINDER_H */
