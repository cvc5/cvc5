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
 * A let binding utility.
 */

#include "printer/let_binding.h"

#include <sstream>

namespace cvc5::internal {

LetBinding::LetBinding(uint32_t thresh)
    : d_thresh(thresh),
      d_context(),
      d_visitList(&d_context),
      d_count(&d_context),
      d_letList(&d_context),
      d_letMap(&d_context)
{
}

uint32_t LetBinding::getThreshold() const { return d_thresh; }

void LetBinding::process(Node n)
{
  if (n.isNull() || d_thresh == 0)
  {
    // value of 0 means do not introduce let
    return;
  }
  // update the count of occurrences
  updateCounts(n);
}

void LetBinding::letify(Node n, std::vector<Node>& letList)
{
  // first, push the context
  pushScope();
  // process the node
  process(n);
  // now, letify
  letify(letList);
}

void LetBinding::letify(std::vector<Node>& letList)
{
  size_t prevSize = d_letList.size();
  // populate the d_letList and d_letMap
  convertCountToLet();
  // add the new entries to the letList
  letList.insert(letList.end(), d_letList.begin() + prevSize, d_letList.end());
}

void LetBinding::pushScope() { d_context.push(); }

void LetBinding::popScope() { d_context.pop(); }

uint32_t LetBinding::getId(Node n) const
{
  NodeIdMap::const_iterator it = d_letMap.find(n);
  if (it == d_letMap.end())
  {
    return 0;
  }
  return (*it).second;
}

Node LetBinding::convert(Node n, const std::string& prefix, bool letTop) const
{
  if (d_letMap.empty())
  {
    return n;
  }
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      uint32_t id = getId(cur);
      // do not letify id 0, or n itself if letTop is false
      if (id > 0 && (cur != n || letTop))
      {
        // make the let variable
        std::stringstream ss;
        ss << prefix << id;
        visited[cur] = nm->mkBoundVar(ss.str(), cur.getType());
      }
      else if (cur.isClosure())
      {
        // do not convert beneath quantifiers
        visited[cur] = cur;
      }
      else
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

void LetBinding::updateCounts(Node n)
{
  NodeIdMap::iterator it;
  std::vector<Node> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    it = d_count.find(cur);
    if (it == d_count.end())
    {
      // do not traverse beneath quantifiers
      if (cur.getNumChildren() == 0 || cur.isClosure())
      {
        d_visitList.push_back(cur);
        d_count[cur] = 1;
        visit.pop_back();
      }
      else
      {
        d_count[cur] = 0;
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else
    {
      if ((*it).second == 0)
      {
        d_visitList.push_back(cur);
      }
      d_count[cur] = (*it).second + 1;
      visit.pop_back();
    }
  } while (!visit.empty());
}

void LetBinding::convertCountToLet()
{
  Assert(d_thresh > 0);
  // Assign ids for those whose d_count is >= d_thresh, traverse in d_visitList
  // in order so that deeper nodes are assigned lower identifiers, which
  // ensures the let list can be printed.
  NodeIdMap::const_iterator itc;
  for (const Node& n : d_visitList)
  {
    if (n.getNumChildren() == 0)
    {
      // do not letify terms with no children
      continue;
    }
    else if (d_letMap.find(n) != d_letMap.end())
    {
      // already letified, perhaps at a lower context
      continue;
    }
    itc = d_count.find(n);
    Assert(itc != d_count.end());
    if ((*itc).second >= d_thresh)
    {
      d_letList.push_back(n);
      // start with id 1
      size_t id = d_letMap.size() + 1;
      d_letMap[n] = id;
    }
  }
}

}  // namespace cvc5::internal
