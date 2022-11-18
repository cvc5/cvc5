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

#include "decision/prop_finder.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::prop;

namespace cvc5::internal {
namespace decision {

PropFindInfo::PropFindInfo(context::Context* c) : d_childIndex(c, 0), d_parentList(c) {}

PropFinder::PropFinder(Env& env,
                       prop::CDCLTSatSolverInterface* ss,
                       prop::CnfStream* cs)
    : EnvObj(env), d_pstate(context()), d_jcache(context(), ss, cs)
{
}

PropFinder::~PropFinder() {}

void PropFinder::addAssertion(TNode n,
                              TNode skolem,
                              bool isLemma,
                              std::vector<TNode>& toPreregister)
{
  if (!skolem.isNull())
  {
    // skolem definitions handled dynamically
    return;
  }
  setRelevant(n, toPreregister);
}

void PropFinder::notifyActiveSkolemDefs(std::vector<TNode>& defs,
                                        std::vector<TNode>& toPreregister)
{
  for (TNode d : defs)
  {
    setRelevant(d, toPreregister);
  }
}

void PropFinder::setRelevant(TNode n, std::vector<TNode>& toPreregister)
{
  // child, parent, desired polarity
  std::vector<std::tuple<TNode, TNode, prop::SatValue> > toVisit;
  toVisit.emplace_back(n, d_null, SAT_VALUE_TRUE);
  std::tuple<TNode, TNode, prop::SatValue> t;
  context::CDInsertHashMap<Node, std::shared_ptr<PropFindInfo> >::const_iterator it;
  TNode curr;
  do
  {
    t = toVisit.back();
    toVisit.pop_back();
    curr = std::get<0>(t);
    d_pstate.find(curr);
  } while (!toVisit.empty());
}

void PropFinder::notifyAsserted(TNode n, std::vector<TNode>& toPreregister)
{
  bool pol = n.getKind() != kind::NOT;
  TNode natom = pol ? n : n[0];
  // set justified
  d_jcache.setValue(natom, pol ? SAT_VALUE_TRUE : SAT_VALUE_FALSE);
  // then, visit parents recursively
  // node, assigned value
  std::vector<TNode> toVisit;
  toVisit.emplace_back(natom);
  context::CDInsertHashMap<Node, std::shared_ptr<PropFindInfo> >::const_iterator it;
  TNode curr;
  do
  {
    curr = toVisit.back();
    toVisit.pop_back();
    d_pstate.find(curr);
    if (d_pstate.find(curr)==d_pstate.end())
    {
      // not watching it
      continue;
    }
    
  } while (!toVisit.empty());
}

}  // namespace decision
}  // namespace cvc5::internal
