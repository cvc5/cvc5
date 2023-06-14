/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of multi-linear inst match generator class.
 */
#include "theory/quantifiers/ematching/inst_match_generator_multi_linear.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/ematching/trigger_trie.h"
#include "theory/quantifiers/term_util.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

InstMatchGeneratorMultiLinear::InstMatchGeneratorMultiLinear(
    Env& env, Trigger* tparent, Node q, std::vector<Node>& pats)
    : InstMatchGenerator(env, tparent, Node::null())
{
  // order patterns to maximize eager matching failures
  std::map<Node, std::vector<Node> > var_contains;
  for (const Node& pat : pats)
  {
    TermUtil::computeInstConstContainsForQuant(q, pat, var_contains[pat]);
  }
  std::map<Node, std::vector<Node> > var_to_node;
  for (std::pair<const Node, std::vector<Node> >& vc : var_contains)
  {
    for (const Node& n : vc.second)
    {
      var_to_node[n].push_back(vc.first);
    }
  }
  std::vector<Node> pats_ordered;
  std::vector<bool> pats_ordered_independent;
  std::map<Node, bool> var_bound;
  size_t patsSize = pats.size();
  while (pats_ordered.size() < patsSize)
  {
    // score is lexographic ( bound vars, shared vars )
    int score_max_1 = -1;
    int score_max_2 = -1;
    unsigned score_index = 0;
    bool set_score_index = false;
    for (size_t i = 0; i < patsSize; i++)
    {
      Node p = pats[i];
      if (std::find(pats_ordered.begin(), pats_ordered.end(), p)
          == pats_ordered.end())
      {
        int score_1 = 0;
        int score_2 = 0;
        for (unsigned j = 0; j < var_contains[p].size(); j++)
        {
          Node v = var_contains[p][j];
          if (var_bound.find(v) != var_bound.end())
          {
            score_1++;
          }
          else if (var_to_node[v].size() > 1)
          {
            score_2++;
          }
        }
        if (!set_score_index || score_1 > score_max_1
            || (score_1 == score_max_1 && score_2 > score_max_2))
        {
          score_index = i;
          set_score_index = true;
          score_max_1 = score_1;
          score_max_2 = score_2;
        }
      }
    }
    Assert(set_score_index);
    // update the variable bounds
    Node mp = pats[score_index];
    std::vector<Node>& vcm = var_contains[mp];
    for (const Node& vc : vcm)
    {
      var_bound[vc] = true;
    }
    pats_ordered.push_back(mp);
    pats_ordered_independent.push_back(score_max_1 == 0);
  }

  Trace("multi-trigger-linear")
      << "Make children for linear multi trigger." << std::endl;
  for (size_t i = 0, poSize = pats_ordered.size(); i < poSize; i++)
  {
    Node po = pats_ordered[i];
    Trace("multi-trigger-linear") << "...make for " << po << std::endl;
    InstMatchGenerator* cimg = getInstMatchGenerator(env, tparent, q, po);
    Assert(cimg != nullptr);
    d_children.push_back(cimg);
    // this could be improved
    if (i == 0)
    {
      cimg->setIndependent();
    }
  }
}

int InstMatchGeneratorMultiLinear::resetChildren()
{
  for (InstMatchGenerator* c : d_children)
  {
    if (!c->reset(Node::null()))
    {
      return -2;
    }
  }
  return 1;
}

bool InstMatchGeneratorMultiLinear::reset(Node eqc)
{
  Assert(eqc.isNull());
  if (options().quantifiers.multiTriggerLinear)
  {
    return true;
  }
  return resetChildren() > 0;
}

int InstMatchGeneratorMultiLinear::getNextMatch(InstMatch& m)
{
  Trace("multi-trigger-linear-debug")
      << "InstMatchGeneratorMultiLinear::getNextMatch : reset " << std::endl;
  if (options().quantifiers.multiTriggerLinear)
  {
    // reset everyone
    int rc_ret = resetChildren();
    if (rc_ret < 0)
    {
      return rc_ret;
    }
  }
  Trace("multi-trigger-linear-debug")
      << "InstMatchGeneratorMultiLinear::getNextMatch : continue match "
      << std::endl;
  Assert(d_next != nullptr);
  int ret_val =
      continueNextMatch(m, InferenceId::QUANTIFIERS_INST_E_MATCHING_MTL);
  if (ret_val > 0)
  {
    Trace("multi-trigger-linear")
        << "Successful multi-trigger instantiation." << std::endl;
    if (options().quantifiers.multiTriggerLinear)
    {
      // now, restrict everyone
      for (size_t i = 0, csize = d_children.size(); i < csize; i++)
      {
        Node mi = d_children[i]->getCurrentMatch();
        Trace("multi-trigger-linear")
            << "   child " << i << " match : " << mi << std::endl;
        d_children[i]->excludeMatch(mi);
      }
    }
  }
  return ret_val;
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
