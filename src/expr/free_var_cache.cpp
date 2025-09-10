/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
  while (i >= d_fv[tn].size())
  {
    Node v = NodeManager::mkBoundVar(tn);
    d_allVars.push_back(v);
    // store its id
    d_fvId[v] = d_fv[tn].size();
    Trace("free-var-cache")
        << "Free variable id " << v << " = " << d_fvId[v] << std::endl;
    d_fv[tn].push_back(v);
  }
  return d_fv[tn][i];
}

TNode FreeVarCache::getFreeVarInc(const TypeNode& tn,
                                  std::map<TypeNode, size_t>& var_count)
{
  size_t index = var_count[tn];
  var_count[tn]++;
  return getFreeVar(tn, index);
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

bool FreeVarCache::hasFreeVar(const Node& n) const
{
  return expr::hasSubterm(n, d_allVars);
}

}  // namespace cvc5::internal
