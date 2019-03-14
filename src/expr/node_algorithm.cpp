/*********************                                                        */
/*! \file node_algorithm.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common algorithms on nodes
 **
 ** This file implements common algorithms applied to nodes, such as checking if
 ** a node contains a free or a bound variable.
 **/

#include "expr/node_algorithm.h"

#include "expr/attribute.h"

namespace CVC4 {
namespace expr {

bool hasSubterm(TNode n, TNode t, bool strict)
{
  if (!strict && n == t)
  {
    return true;
  }

  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> toProcess;

  toProcess.push_back(n);

  for (unsigned i = 0; i < toProcess.size(); ++i)
  {
    TNode current = toProcess[i];
    if (current.hasOperator() && current.getOperator() == t)
    {
      return true;
    }
    for (unsigned j = 0, j_end = current.getNumChildren(); j < j_end; ++j)
    {
      TNode child = current[j];
      if (child == t)
      {
        return true;
      }
      if (visited.find(child) != visited.end())
      {
        continue;
      }
      else
      {
        visited.insert(child);
        toProcess.push_back(child);
      }
    }
  }

  return false;
}

bool hasSubtermMulti(TNode n, TNode t)
{
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::unordered_map<TNode, bool, TNodeHashFunction> contains;
  std::unordered_map<TNode, bool, TNodeHashFunction>::iterator it;
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
      if (cur == t)
      {
        visited[cur] = true;
        contains[cur] = true;
      }
      else
      {
        visited[cur] = false;
        visit.push_back(cur);
        for (const Node& cc : cur)
        {
          visit.push_back(cc);
        }
      }
    }
    else if (!it->second)
    {
      bool doesContain = false;
      for (const Node& cn : cur)
      {
        it = contains.find(cn);
        Assert(it != visited.end());
        if (it->second)
        {
          if (doesContain)
          {
            // two children have t, return true
            return true;
          }
          doesContain = true;
        }
      }
      contains[cur] = doesContain;
      visited[cur] = true;
    }
  } while (!visit.empty());
  return false;
}

struct HasBoundVarTag
{
};
struct HasBoundVarComputedTag
{
};
/** Attribute true for expressions with bound variables in them */
typedef expr::Attribute<HasBoundVarTag, bool> HasBoundVarAttr;
typedef expr::Attribute<HasBoundVarComputedTag, bool> HasBoundVarComputedAttr;

bool hasBoundVar(TNode n)
{
  if (!n.getAttribute(HasBoundVarComputedAttr()))
  {
    bool hasBv = false;
    if (n.getKind() == kind::BOUND_VARIABLE)
    {
      hasBv = true;
    }
    else
    {
      for (auto i = n.begin(); i != n.end() && !hasBv; ++i)
      {
        hasBv = hasBoundVar(*i);
      }
    }
    if (!hasBv && n.hasOperator())
    {
      hasBv = hasBoundVar(n.getOperator());
    }
    n.setAttribute(HasBoundVarAttr(), hasBv);
    n.setAttribute(HasBoundVarComputedAttr(), true);
    Debug("bva") << n << " has bva : " << n.getAttribute(HasBoundVarAttr())
                 << std::endl;
    return hasBv;
  }
  return n.getAttribute(HasBoundVarAttr());
}

bool hasFreeVar(TNode n)
{
  std::unordered_set<Node, NodeHashFunction> fvs;
  return getFreeVariables(n, fvs, false);
}

bool getFreeVariables(TNode n,
                      std::unordered_set<Node, NodeHashFunction>& fvs,
                      bool computeFv)
{
  std::unordered_set<TNode, TNodeHashFunction> bound_var;
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    // can skip if it doesn't have a bound variable
    if (!hasBoundVar(cur))
    {
      continue;
    }
    Kind k = cur.getKind();
    bool isQuant = k == kind::FORALL || k == kind::EXISTS || k == kind::LAMBDA
                   || k == kind::CHOICE;
    std::unordered_map<TNode, bool, TNodeHashFunction>::iterator itv =
        visited.find(cur);
    if (itv == visited.end())
    {
      if (k == kind::BOUND_VARIABLE)
      {
        if (bound_var.find(cur) == bound_var.end())
        {
          if (computeFv)
          {
            fvs.insert(cur);
          }
          else
          {
            return true;
          }
        }
      }
      else if (isQuant)
      {
        for (const TNode& cn : cur[0])
        {
          // should not shadow
          Assert(bound_var.find(cn) == bound_var.end());
          bound_var.insert(cn);
        }
        visit.push_back(cur);
      }
      // must visit quantifiers again to clean up below
      visited[cur] = !isQuant;
      if (cur.hasOperator())
      {
        visit.push_back(cur.getOperator());
      }
      for (const TNode& cn : cur)
      {
        visit.push_back(cn);
      }
    }
    else if (!itv->second)
    {
      Assert(isQuant);
      for (const TNode& cn : cur[0])
      {
        bound_var.erase(cn);
      }
      visited[cur] = true;
    }
  } while (!visit.empty());

  return !fvs.empty();
}

void getSymbols(TNode n, std::unordered_set<Node, NodeHashFunction>& syms)
{
  std::unordered_set<TNode, TNodeHashFunction> visited;
  getSymbols(n, syms, visited);
}

void getSymbols(TNode n,
                std::unordered_set<Node, NodeHashFunction>& syms,
                std::unordered_set<TNode, TNodeHashFunction>& visited)
{
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.isVar() && cur.getKind() != kind::BOUND_VARIABLE)
      {
        syms.insert(cur);
      }
      if (cur.hasOperator())
      {
        visit.push_back(cur.getOperator());
      }
      for (TNode cn : cur)
      {
        visit.push_back(cn);
      }
    }
  } while (!visit.empty());
}

Node substituteCaptureAvoiding(Node node, Node replacement) const
{
  if (node == *this)
  {
    return replacement;
  }
  std::vector<Node> source;
  std::vector<Node> dest;
  source.push_back(node);
  dest.push_back(replacement);
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  return substituteCaptureAvoiding(source, dest, cache);
}

Node substituteCaptureAvoiding(
    Node node,
    Node replacement,
    std::unordered_map<Node, Node, NodeHashFunction>& cache) const
{
  std::vector<Node> source;
  std::vector<Node> dest;
  source.push_back(node);
  dest.push_back(replacement);
  return substituteCaptureAvoiding(source, dest, cache);
}

Node substituteCaptureAvoiding(std::vector<Node>& source,
                               std::vector<Node>& dest) const
{
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  return substituteCaptureAvoiding(source, dest, cache);
}

Node substituteCaptureAvoiding(
    std::vector<Node>& source,
    std::vector<Node>& dest,
    std::unordered_map<Node, Node, NodeHashFunction>& cache) const
{
  // in cache?
  typename std::unordered_map<Node, Node, NodeHashFunction>::const_iterator i =
      cache.find(*this);
  if (i != cache.end())
  {
    return (*i).second;
  }

  // otherwise compute
  Assert(source.size() == dest.size(),
         "Substitution domain and range must be equal size");

  auto it = std::find(source.begin(), source.end(), (*this));
  if (it != source.end())
  {
    Assert(std::distance(source.begin(), it) >= 0
           && std::distance(source.begin(), it) < dest.size());
    Node n = dest[std::distance(source.begin(), it)];
    cache[*this] = n;
    return n;
  }
  if (getNumChildren() == 0)
  {
    cache[*this] = *this;
    return *this;
  }
  bool binder = isClosure();
  // if binder, rename variables to avoid capture
  if (binder)
  {
    std::vector<Node> vars;
    std::vector<Node> renames;

    NodeManager* nm = NodeManager::currentNM();
    for (const Node& v : (*this)[0])
    {
      vars.push_back(v);
      renames.push_back(nm->mkBoundVar(v.getType()));
    }
    // have new vars -> renames subs in the beginning of current sub
    source.insert(source.begin(), vars.begin(), vars.end());
    dest.insert(dest.begin(), renames.begin(), renames.end());
  }
  NodeBuilder<> nb(getKind());
  if (getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    // push the operator
    nb << getOperator().substituteCaptureAvoiding(source, dest, cache);
  }
  for (const_iterator i = begin(), iend = end(); i != iend; ++i)
  {
    nb << (*i).substituteCaptureAvoiding(source, dest, cache);
  }
  Node n = nb;
  cache[*this] = n;

  // remove renaming
  if (binder)
  {
    // remove beginning of sub which correspond to renaming of variables in
    // this binder
    unsigned nchildren = (*this)[0].getNumChildren();
    source.erase(source.begin(), source.begin() + nchildren);
    dest.erase(dest.begin(), dest.begin() + nchildren);
  }
  return n;
}

}  // namespace expr
}  // namespace CVC4
