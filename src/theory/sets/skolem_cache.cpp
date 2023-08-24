/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of a cache of skolems for theory of sets.
 */

#include "theory/sets/skolem_cache.h"

#include "expr/skolem_manager.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace sets {

SkolemCache::SkolemCache(Rewriter* rr) : d_rewriter(rr) {}

Node SkolemCache::mkTypedSkolemCached(
    TypeNode tn, Node a, Node b, SkolemId id, const char* c)
{
  if (d_rewriter != nullptr)
  {
    a = a.isNull() ? a : d_rewriter->rewrite(a);
    b = b.isNull() ? b : d_rewriter->rewrite(b);
  }
  std::map<SkolemId, Node>::iterator it = d_skolemCache[a][b].find(id);
  if (it == d_skolemCache[a][b].end())
  {
    SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
    Node sk;
    if (id == SkolemId::SK_PURIFY)
    {
      Assert(a.getType() == tn);
      sk = sm->mkPurifySkolem(a);
    }
    else
    {
      sk = sm->mkDummySkolem(c, tn, "sets skolem");
    }
    d_skolemCache[a][b][id] = sk;
    d_allSkolems.insert(sk);
    return sk;
  }
  return it->second;
}
Node SkolemCache::mkTypedSkolemCached(TypeNode tn,
                                      Node a,
                                      SkolemId id,
                                      const char* c)
{
  return mkTypedSkolemCached(tn, a, Node::null(), id, c);
}

Node SkolemCache::mkTypedSkolem(TypeNode tn, const char* c)
{
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  Node n = sm->mkDummySkolem(c, tn, "sets skolem");
  d_allSkolems.insert(n);
  return n;
}

bool SkolemCache::isSkolem(Node n) const
{
  return d_allSkolems.find(n) != d_allSkolems.end();
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
