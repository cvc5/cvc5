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
 * Skolem definition manager.
 */

#include "prop/skolem_def_manager.h"

namespace cvc5::internal {
namespace prop {

SkolemDefManager::SkolemDefManager(context::Context* context,
                                   context::UserContext* userContext)
    : d_skDefs(userContext), d_skActive(context), d_hasSkolems(userContext)
{
}

SkolemDefManager::~SkolemDefManager() {}

void SkolemDefManager::notifySkolemDefinition(TNode skolem, Node def)
{
  // Notice that skolem should have kind SKOLEM
  Trace("sk-defs") << "notifySkolemDefinition: " << def << " for " << skolem
                   << std::endl;
  // in very rare cases, a skolem may be generated twice for terms that are
  // equivalent up to purification
  if (d_skDefs.find(skolem) == d_skDefs.end())
  {
    // should not have already computed whether the skolem has skolems or
    // otherwise we should have marked that we have skolems, or else
    // our computation of hasSkolems is wrong after adding this definition
    Assert(d_hasSkolems.find(skolem) == d_hasSkolems.end()
           || d_hasSkolems[skolem]);
    d_skDefs.insert(skolem, def);
  }
}

TNode SkolemDefManager::getDefinitionForSkolem(TNode skolem) const
{
  NodeNodeMap::const_iterator it = d_skDefs.find(skolem);
  Assert(it != d_skDefs.end()) << "No skolem def for " << skolem;
  return it->second;
}

void SkolemDefManager::notifyAsserted(TNode literal,
                                      std::vector<TNode>& activatedSkolems)
{
  if (d_skActive.size() == d_skDefs.size())
  {
    // already activated all skolems
    return;
  }
  std::unordered_set<Node> defs;
  getSkolems(literal, defs, true);
  Trace("sk-defs") << "notifyAsserted: " << literal << " has skolems " << defs
                   << std::endl;
  for (const Node& d : defs)
  {
    if (d_skActive.find(d) != d_skActive.end())
    {
      // already active
      continue;
    }
    d_skActive.insert(d);
    Trace("sk-defs") << "...activate " << d << std::endl;
    // add its definition to the activated list
    activatedSkolems.push_back(d);
  }
}

bool SkolemDefManager::hasSkolems(TNode n)
{
  Trace("sk-defs-debug") << "Compute has skolems for " << n << std::endl;
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
  NodeBoolMap::const_iterator itn;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    itn = d_hasSkolems.find(cur);
    if (itn != d_hasSkolems.end())
    {
      visit.pop_back();
      // already computed
      continue;
    }
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited.insert(cur);
      if (cur.getNumChildren() == 0)
      {
        visit.pop_back();
        Kind ck = cur.getKind();
        // We have skolems if we are a skolem that has a definition, or
        // we are a Boolean term variable. For Boolean term variables, we do
        // not make this test depend on whether the skolem has a definition,
        // since that is prone to change if the Boolean term variable was
        // introduced in a lemma prior to its definition being introduced.
        // This is for example the case in strings reduction for Booleans,
        // ground term purification for E-matching, etc.
        d_hasSkolems[cur] = (ck == kind::SKOLEM
                             && (d_skDefs.find(cur) != d_skDefs.end()
                                 || cur.getType().isBoolean()));
      }
      else
      {
        if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
        {
          visit.push_back(cur.getOperator());
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else
    {
      visit.pop_back();
      bool hasSkolem;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED
          && d_hasSkolems[cur.getOperator()])
      {
        hasSkolem = true;
      }
      else
      {
        hasSkolem = false;
        for (TNode i : cur)
        {
          Assert(d_hasSkolems.find(i) != d_hasSkolems.end());
          if (d_hasSkolems[i])
          {
            hasSkolem = true;
            break;
          }
        }
      }
      d_hasSkolems[cur] = hasSkolem;
    }
  } while (!visit.empty());
  Assert(d_hasSkolems.find(n) != d_hasSkolems.end());
  return d_hasSkolems[n];
}

void SkolemDefManager::getSkolems(TNode n,
                                  std::unordered_set<Node>& skolems,
                                  bool useDefs)
{
  NodeNodeMap::const_iterator itd;
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (!hasSkolems(cur))
    {
      // does not have skolems, continue
      continue;
    }
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited.insert(cur);
      if (cur.isVar())
      {
        itd = d_skDefs.find(cur);
        if (itd != d_skDefs.end())
        {
          skolems.insert(useDefs ? itd->second : Node(cur));
        }
        continue;
      }
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        visit.push_back(cur.getOperator());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

}  // namespace prop
}  // namespace cvc5::internal
