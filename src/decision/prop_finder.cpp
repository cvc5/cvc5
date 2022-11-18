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

PropFindInfo::PropFindInfo(context::Context* c) : d_parentList(c) {}

PropFinder::PropFinder(Env& env,
                       prop::CDCLTSatSolverInterface* ss,
                       prop::CnfStream* cs)
    : EnvObj(env), d_satSolver(ss), d_cnfStream(cs), d_pstate(context())
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
  std::tuple<TNode, TNode, prop::SatValue> curr;
  do
  {
    curr = toVisit.back();
    toVisit.pop_back();
  } while (!toVisit.empty());
}

void PropFinder::notifyAsserted(TNode n, std::vector<TNode>& toPreregister)
{
  // TODO
  Node natom = n.getKind() == kind::NOT ? n[0] : n;
  toPreregister.push_back(natom);
}

}  // namespace decision
}  // namespace cvc5::internal
