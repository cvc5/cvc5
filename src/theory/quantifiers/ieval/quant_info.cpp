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
 * Info per quantified formula in instantiation evaluator.
 */

#include "theory/quantifiers/ieval/quant_info.h"

#include "expr/node_algorithm.h"
#include "expr/term_canonize.h"
#include "theory/quantifiers/ematching/trigger_term_info.h"
#include "theory/quantifiers/term_database.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

QuantInfo::QuantInfo(context::Context* c)
    : d_isActive(c, true), d_maybeConflict(c, true), d_unassignedVars(c, 0)
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

  for (const std::pair<const TNode, std::vector<Node>>& r : d_req)
  {
    d_reqTerms.push_back(r.first);
  }

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
    for (const std::pair<const TNode, std::vector<Node>>& r : d_req)
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
  Node eqc = NodeManager::currentNM()->mkConst(!pol);
  addMatchTermReq(cur, eqc, true);
}

void QuantInfo::addMatchTermReq(TNode t, Node eqc, bool isEq)
{
  // notice that in rare cases, t may have no free variables, e.g.
  // if miniscoping is disabled, or there is a ground subterm in a non-entailed
  // position.

  // if not equal, make into disequality constraint (not (= t eqc))
  if (!isEq)
  {
    Assert(!eqc.isNull());
    eqc = t.eqNode(eqc).notNode();
  }
  std::vector<Node>& reqs = d_req[t];
  if (std::find(reqs.begin(), reqs.end(), eqc) == reqs.end())
  {
    reqs.push_back(eqc);
  }
}

const std::map<TNode, std::vector<Node>>& QuantInfo::getConstraints() const
{
  return d_req;
}

const std::vector<TNode>& QuantInfo::getConstraintTerms() const
{
  return d_reqTerms;
}

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

bool QuantInfo::isTraverseTerm(TNode n) { return !n.isClosure(); }

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
