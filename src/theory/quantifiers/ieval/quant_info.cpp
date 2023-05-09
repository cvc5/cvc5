/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Info per quantified formula in instantiation evaluator.
 */

#include "theory/quantifiers/ieval/quant_info.h"

#include <sstream>

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

QuantInfo::QuantInfo(context::Context* c)
    : d_isActive(c, true),
      d_maybeConflict(c, true),
      d_unassignedVars(c, 0),
      d_failReq(c)
{
}

void QuantInfo::initialize(TNode q, Node body)
{
  Assert(q.getKind() == FORALL);
  d_quant = q;

  Trace("ieval-quant-debug")
      << "Register quant " << d_quant.getId() << " : " << d_quant << std::endl;

  // canonize the body of the quantified formula
  Trace("ieval-quant-debug") << "Get body..." << std::endl;
  d_body = body;

  // compute matching requirements
  Trace("ieval-quant-debug") << "Compute constraints..." << std::endl;
  std::unordered_set<TNode> processed;
  std::unordered_set<TNode>::iterator itp;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(d_body);
  do
  {
    cur = visit.back();
    visit.pop_back();
    itp = processed.find(cur);
    if (itp == processed.end())
    {
      processed.insert(cur);
      // process the match requirement for (disjunct) cur
      computeMatchReq(cur, visit);
    }
  } while (!visit.empty());

  d_unassignedVars = q[0].getNumChildren();
  // debug print
  Trace("ieval-quant") << toStringDebug();
}

std::string QuantInfo::toStringDebug() const
{
  std::stringstream ss;
  ss << "--- QuantInfo for " << d_quant.getId() << std::endl;
  ss << "Body: " << d_body << std::endl;
  ss << "Constraints:" << std::endl;
  if (d_req.empty())
  {
    ss << "  (none)" << std::endl;
  }
  else
  {
    for (const std::pair<const TNode, bool>& r : d_req)
    {
      ss << "  " << r.first << " -> " << r.second << std::endl;
    }
  }
  return ss.str();
}

void QuantInfo::computeMatchReq(TNode cur, std::vector<TNode>& visit)
{
  Assert(cur.getType().isBoolean());
  bool pol = true;
  Kind k = cur.getKind();
  Assert(k != IMPLIES);
  if (k == OR)
  {
    // decompose OR
    visit.insert(visit.end(), cur.begin(), cur.end());
    return;
  }
  else if (k == NOT)
  {
    pol = false;
    cur = cur[0];
    k = cur.getKind();
    // double negations should already be eliminated
    Assert(k != NOT);
    // should be NNF
    Assert(k != AND);
  }
  // required to falsify
  d_req[cur] = !pol;
}

const std::map<TNode, bool>& QuantInfo::getConstraints() const { return d_req; }

size_t QuantInfo::getNumUnassignedVars() const
{
  return d_unassignedVars.get();
}

void QuantInfo::decrementUnassignedVar()
{
  d_unassignedVars = d_unassignedVars - 1;
}

bool QuantInfo::isActive() const { return d_isActive.get(); }

void QuantInfo::setActive(bool val) { d_isActive = val; }

void QuantInfo::setNoConflict() { d_maybeConflict = false; }

bool QuantInfo::isMaybeConflict() const { return d_maybeConflict.get(); }

void QuantInfo::setFailureConstraint(TNode c) { d_failReq = c; }

TNode QuantInfo::getFailureConstraint() const { return d_failReq.get(); }

bool QuantInfo::isTraverseTerm(TNode n) { return !n.isClosure(); }

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
