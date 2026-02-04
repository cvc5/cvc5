/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Algorithms used by the Alethe post processor
 */

#include "proof/alethe/alethe_post_processor_algorithm.h"

#include "expr/nary_term_util.h"
#include "proof/alethe/alethe_post_processor.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

namespace proof {

// Closely follows the algorithm implemented in Carcara
// (https://github.com/ufmg-smite/carcara). Note that when removing duplicates
// we keep the first occurence.
Node applyAcSimp(Env& env, std::map<Node, Node>& cache, Node term)
{
  NodeManager* nm = env.getNodeManager();
  auto it = cache.find(term);
  if (it != cache.end())
  {
    return it->second;
  }
  if (term.getNumChildren() == 0)
  {
    return term;
  }
  if (term.getMetaKind() == metakind::PARAMETERIZED)
  {
    // not supported
    Trace("alethe-proof") << "... reached a parameterized operator during "
                             "flattening the term which is not supported. Will "
                             "not flatten any subterm of the current term "
                          << term << "\n";
    return term;
  }

  Kind k = term.getKind();
  Node ac_term;
  std::vector<Node> ac_children;
  if (k == Kind::AND || k == Kind::OR)
  {
    for (const Node& child : term)
    {
      Node ac_child = applyAcSimp(env, cache, child);
      Kind k_ac_child = ac_child.getKind();
      if (k_ac_child == k)
      {
        // flatten
        for (const Node& c : ac_child)
        {
          if (std::find(ac_children.begin(), ac_children.end(), c)
              == ac_children.end())
          {
            ac_children.push_back(c);
          }
        }
      }
      else
      {
        // do not flatten, add entire child term
        if (std::find(ac_children.begin(), ac_children.end(), ac_child)
            == ac_children.end())
        {
          ac_children.push_back(ac_child);
        }
      }
    }
    if (ac_children.size() == 1)
    {
      // duplicate removal let to binary term with only one child
      return ac_children[0];
    }
    ac_term = nm->mkNode(k, ac_children);
  }
  else
  {
    for (const Node& child : term)
    {
      ac_children.push_back(applyAcSimp(env, cache, child));
    }
    if (k == Kind::APPLY_UF)
    {
      ac_children.insert(ac_children.begin(), term.getOperator());
    }
    ac_term = nm->mkNode(k, ac_children);
  }
  cache[term] = ac_term;
  return ac_term;
}

}  // namespace proof
}  // namespace cvc5::internal
