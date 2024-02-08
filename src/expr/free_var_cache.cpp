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
 * A class for allocating a list of free variables
 */
#include "expr/free_var_cache.h"

#include "expr/node_algorithm.h"

namespace cvc5::internal {

TNode FreeVarCache::getFreeVar(const TypeNode& tn, size_t i)
{
  return getFreeVar(tn, i, tn);
}

TNode FreeVarCache::getFreeVar(const TypeNode& tn,
                               size_t i,
                               const TypeNode& stn)
{
  NodeManager* nm = NodeManager::currentNM();
  while (i >= d_fv[stn].size())
  {
    Node v = nm->mkBoundVar(tn);
    d_allVars.push_back(v);
    // store its id, which is unique per builtin type, regardless of how it is
    // otherwise cached.
    d_fvId[v] = d_fv[stn].size();
    Trace("free-var-cache") << "Free variable id " << v << " = " << d_fvId[v]
                            << ", " << stn << std::endl;
    d_fv[stn].push_back(v);
  }
  return d_fv[stn][i];
}

TNode FreeVarCache::getFreeVarInc(const TypeNode& tn,
                                  std::map<TypeNode, size_t>& var_count)
{
  return getFreeVarInc(tn, var_count, tn);
}

TNode FreeVarCache::getFreeVarInc(const TypeNode& tn,
                                  std::map<TypeNode, size_t>& var_count,
                                  const TypeNode& stn)
{
  std::map<TypeNode, size_t>::iterator it = var_count.find(stn);
  if (it == var_count.end())
  {
    var_count[stn] = 1;
    return getFreeVar(tn, 0, stn);
  }
  size_t index = it->second;
  var_count[stn]++;
  return getFreeVar(tn, index, stn);
}

bool FreeVarCache::isFreeVar(const Node& n) const
{
  return d_fvId.find(n) != d_fvId.end();
}

size_t FreeVarCache::getFreeVarId(const Node& n) const
{
  std::map<Node, size_t>::const_iterator it = d_fvId.find(n);
  if (it == d_fvId.end())
  {
    Assert(false) << "FreeVarCache::isFreeVar: " << n
                  << " is not a cached free variable.";
    return 0;
  }
  return it->second;
}

bool FreeVarCache::hasFreeVar(const Node& n)
{
  return expr::hasSubterm(n, d_allVars);
}

}  // namespace cvc5::internal
