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
 * Skolem definition manager.
 */

#include "prop/skolem_def_manager.h"

#include "expr/attribute.h"

namespace cvc5 {
namespace prop {

SkolemDefManager::SkolemDefManager(context::Context* context,
                                   context::UserContext* userContext)
    : d_skDefs(userContext), d_skActive(context)
{
}

SkolemDefManager::~SkolemDefManager() {}

void SkolemDefManager::notifySkolemDefinition(TNode skolem, Node def)
{
  // Notice that skolem may have kind SKOLEM or BOOLEAN_TERM_VARIABLE
  Trace("sk-defs") << "notifySkolemDefinition: " << def << " for " << skolem
                   << std::endl;
  // in very rare cases, a skolem may be generated twice for terms that are
  // equivalent up to purification
  if (d_skDefs.find(skolem) == d_skDefs.end())
  {
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
                                      std::vector<TNode>& activatedSkolems,
                                      bool useDefs)
{
  std::unordered_set<Node> skolems;
  getSkolems(literal, skolems);
  for (const Node& k : skolems)
  {
    if (d_skActive.find(k) != d_skActive.end())
    {
      // already active
      continue;
    }
    d_skActive.insert(k);
    if (useDefs)
    {
      // add its definition to the activated list
      NodeNodeMap::const_iterator it = d_skDefs.find(k);
      Assert(it != d_skDefs.end());
      activatedSkolems.push_back(it->second);
    }
    else
    {
      // add to the activated list
      activatedSkolems.push_back(k);
    }
  }
}

struct HasSkolemTag
{
};
struct HasSkolemComputedTag
{
};
/** Attribute true for nodes with skolems in them */
typedef expr::Attribute<HasSkolemTag, bool> HasSkolemAttr;
/** Attribute true for nodes where we have computed the above attribute */
typedef expr::Attribute<HasSkolemComputedTag, bool> HasSkolemComputedAttr;

bool SkolemDefManager::hasSkolems(TNode n) const
{
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    if (cur.getAttribute(HasSkolemComputedAttr()))
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
        bool hasSkolem = false;
        if (cur.isVar())
        {
          hasSkolem = (d_skDefs.find(cur) != d_skDefs.end());
        }
        cur.setAttribute(HasSkolemAttr(), hasSkolem);
        cur.setAttribute(HasSkolemComputedAttr(), true);
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else
    {
      visit.pop_back();
      bool hasSkolem = false;
      for (TNode i : cur)
      {
        Assert(i.getAttribute(HasSkolemComputedAttr()));
        if (i.getAttribute(HasSkolemAttr()))
        {
          hasSkolem = true;
          break;
        }
      }
      cur.setAttribute(HasSkolemAttr(), hasSkolem);
      cur.setAttribute(HasSkolemComputedAttr(), true);
    }
  } while (!visit.empty());
  Assert(n.getAttribute(HasSkolemComputedAttr()));
  return n.getAttribute(HasSkolemAttr());
}

void SkolemDefManager::getSkolems(TNode n,
                                  std::unordered_set<Node>& skolems) const
{
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
        if (d_skDefs.find(cur) != d_skDefs.end())
        {
          skolems.insert(cur);
        }
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());
}

}  // namespace prop
}  // namespace cvc5
