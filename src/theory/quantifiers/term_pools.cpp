/*********************                                                        */
/*! \file term_pools.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utilities for term enumeration
 **/

#include "theory/quantifiers/term_pools.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

void TermPoolDomain::initialize() { d_terms.clear(); }
void TermPoolDomain::add(Node n) { d_terms.insert(n); }

void TermPoolQuantInfo::initialize()
{
d_instAddToPool.clear();
d_skolemAddToPool.clear();
}

void TermPools::registerQuantifier(Node q) {
  if (q.getNumChildren()<3)
  {
    return;
  }
  TermPoolQuantInfo& qi = d_qinfo[q];
  qi.initialize();
  for (const Node& p : q[2])
  {
    Kind pk = p.getKind();
    if (pk==kind::INST_ADD_TO_POOL)
    {
      qi.d_instAddToPool.push_back(p);
    }
    else if (pk==kind::SKOLEM_ADD_TO_POOL)
    {
      qi.d_skolemAddToPool.push_back(p);
    }
  }
  if (qi.d_instAddToPool.empty() && qi.d_skolemAddToPool.empty())
  {
    d_qinfo.erase(q);
  }
}

std::string TermPools::identify() { return "TermPools"; }

void TermPools::registerPool(Node p, const std::vector<Node>& initValue)
{
  TermPoolDomain& d = d_pools[p];
  d.initialize();
  d.d_terms.insert(initValue.begin(), initValue.end());
}

void TermPools::addToPool(Node n, Node p)
{
  TermPoolDomain& dom = getDomain(p);
  dom.add(n);
}

TermPoolDomain& TermPools::getDomain(Node p) { return d_pools[p]; }

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
  std::map<Node, TermPoolQuantInfo>::iterator it = d_qinfo.find(q);
  if (it == d_qinfo.end())
  {
    // does not impact
    return;
  }
  std::vector<Node>& cmds = isInst = it->second.d_instAddToPool : it->second.d_skolemAddToPool;
  for (const Node& c : cmds)
  {
    
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
