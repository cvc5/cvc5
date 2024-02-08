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

namespace cvc5::internal {

TNode TermDbSygus::getFreeVar(const TypeNode& tn, size_t i, size_t vclass)
{
  unsigned sindex = 0;
  std::pair<TypeNode, size_t> key(tn, vclass);
  NodeManager* nm = NodeManager::currentNM();
  while (i >= d_fv[tn].size())
  {
    Assert(!vtn.isNull());
    Node v = nm->mkBoundVar(tn);
    d_allVars.push_back(v);
    // store its id, which is unique per builtin type, regardless of how it is
    // otherwise cached.
    d_fvId[v] = d_fv[key].size();
    Trace("free-var-cache") << "Free variable id " << v << " = " << d_fvId[v]
                            << ", " << tn << std::endl;
    d_fv[key].push_back(v);
  }
  return d_fv[key][i];
}

TNode TermDbSygus::getFreeVarInc(
    const TypeNode& tn,
    std::map<std::pair<TypeNode, size_t>, size_t>& var_count,
    size_t vclass)
{
  std::pair<TypeNode, size_t> key(tn, vclass);
  std::map<TypeNode, int>::iterator it = var_count.find(key);
  if (it == var_count.end())
  {
    var_count[key] = 1;
    return getFreeVar(tn, 0, vclass);
  }
  size_t index = it->second;
  var_count[key]++;
  return getFreeVar(tn, index, vclass);
}

bool TermDbSygus::isFreeVar(const Node& n) const
{
  return d_fvId.find(n) != d_fvId.end();
}

size_t TermDbSygus::getFreeVarId(const Node& n) const
{
  std::map<Node, size_t>::const_iterator it = d_fvId.find(n);
  if (it == d_fvId.end())
  {
    Assert(false) << "TermDbSygus::isFreeVar: " << n
                  << " is not a cached free variable.";
    return 0;
  }
  return it->second;
}

bool TermDbSygus::hasFreeVar(const Node& n)
{
  return expr::hasSubterm(n, d_allVars);
}

}  // namespace cvc5::internal
