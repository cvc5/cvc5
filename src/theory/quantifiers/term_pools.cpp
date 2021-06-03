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
 * Utilities for term enumeration.
 */

#include "theory/quantifiers/term_pools.h"

#include "theory/quantifiers/quantifiers_state.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

void TermPoolDomain::initialize() { d_terms.clear(); }
void TermPoolDomain::add(Node n)
{
  if (std::find(d_terms.begin(), d_terms.end(), n) == d_terms.end())
  {
    d_terms.push_back(n);
  }
}

void TermPoolQuantInfo::initialize()
{
  d_instAddToPool.clear();
  d_skolemAddToPool.clear();
}

TermPools::TermPools(QuantifiersState& qs) : d_qs(qs) {}

bool TermPools::reset(Theory::Effort e)
{
  for (std::pair<const Node, TermPoolDomain>& p : d_pools)
  {
    p.second.d_currTerms.clear();
  }
  return true;
}

void TermPools::registerQuantifier(Node q)
{
  if (q.getNumChildren() < 3)
  {
    return;
  }
  TermPoolQuantInfo& qi = d_qinfo[q];
  qi.initialize();
  for (const Node& p : q[2])
  {
    Kind pk = p.getKind();
    if (pk == kind::INST_ADD_TO_POOL)
    {
      qi.d_instAddToPool.push_back(p);
    }
    else if (pk == kind::SKOLEM_ADD_TO_POOL)
    {
      qi.d_skolemAddToPool.push_back(p);
    }
  }
  if (qi.d_instAddToPool.empty() && qi.d_skolemAddToPool.empty())
  {
    d_qinfo.erase(q);
  }
}

std::string TermPools::identify() const { return "TermPools"; }

void TermPools::registerPool(Node p, const std::vector<Node>& initValue)
{
  TermPoolDomain& d = d_pools[p];
  d.initialize();
  for (const Node& i : initValue)
  {
    Assert(i.getType().isComparableTo(p.getType().getSetElementType()));
    d.add(i);
  }
}

void TermPools::getTermsForPool(Node p, std::vector<Node>& terms)
{
  // for now, we assume p is a variable
  Assert(p.isVar());
  TermPoolDomain& dom = d_pools[p];
  if (dom.d_terms.empty())
  {
    return;
  }
  // if we have yet to compute terms on this round
  if (dom.d_currTerms.empty())
  {
    std::unordered_set<Node> reps;
    // eliminate modulo equality
    for (const Node& t : dom.d_terms)
    {
      Node r = d_qs.getRepresentative(t);
      if (reps.find(r) == reps.end())
      {
        reps.insert(r);
        dom.d_currTerms.push_back(t);
      }
    }
    Trace("pool-terms") << "* Domain for pool " << p << " is "
                        << dom.d_currTerms << std::endl;
  }
  terms.insert(terms.end(), dom.d_currTerms.begin(), dom.d_currTerms.end());
}

void TermPools::processInstantiation(Node q, const std::vector<Node>& terms)
{
  processInternal(q, terms, true);
}

void TermPools::processSkolemization(Node q, const std::vector<Node>& skolems)
{
  processInternal(q, skolems, false);
}

void TermPools::processInternal(Node q,
                                const std::vector<Node>& ts,
                                bool isInst)
{
  Assert(q.getKind() == kind::FORALL);
  std::map<Node, TermPoolQuantInfo>::iterator it = d_qinfo.find(q);
  if (it == d_qinfo.end())
  {
    // does not impact
    return;
  }
  std::vector<Node> vars(q[0].begin(), q[0].end());
  Assert(vars.size() == ts.size());
  std::vector<Node>& cmds =
      isInst ? it->second.d_instAddToPool : it->second.d_skolemAddToPool;
  for (const Node& c : cmds)
  {
    Assert(c.getNumChildren() == 2);
    Node t = c[0];
    // substitute the term
    Node st = t.substitute(vars.begin(), vars.end(), ts.begin(), ts.end());
    // add to pool
    Trace("pool-terms") << "Due to "
                        << (isInst ? "instantiation" : "skolemization")
                        << ", add " << st << " to pool " << c[1] << std::endl;
    TermPoolDomain& dom = d_pools[c[1]];
    dom.d_terms.push_back(st);
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
