/*********************                                                        */
/*! \file relevance_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of relevance manager.
 **/

#include "theory/relevance_manager.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

RelevanceManager::RelevanceManager(context::UserContext* userContext,
                                   Valuation val)
    : d_val(val), d_input(userContext), d_computed(false), d_success(false)
{
}

void RelevanceManager::notifyPreprocessedAssertions(
    const std::vector<Node>& assertions)
{
  // add to input list, which is user-context dependent
  std::vector<Node> toProcess;
  for (const Node& a : assertions)
  {
    if (a.getKind() == AND)
    {
      // split top-level AND
      for (const Node& ac : a)
      {
        toProcess.push_back(ac);
      }
    }
    else
    {
      d_input.push_back(a);
    }
  }
  addAssertionsInternal(toProcess);
}

void RelevanceManager::notifyPreprocessedAssertion(Node n)
{
  std::vector<Node> toProcess;
  toProcess.push_back(n);
  addAssertionsInternal(toProcess);
}

void RelevanceManager::addAssertionsInternal(std::vector<Node>& toProcess)
{
  size_t i = 0;
  while (i < toProcess.size())
  {
    Node a = toProcess[i];
    if (a.getKind() == AND)
    {
      // split AND
      for (const Node& ac : a)
      {
        toProcess.push_back(ac);
      }
    }
    else
    {
      // note that a could be a literal, in which case we could add it to
      // an "always relevant" set here.
      d_input.push_back(a);
    }
    i++;
  }
}

void RelevanceManager::resetRound()
{
  d_computed = false;
  d_rset.clear();
}

void RelevanceManager::computeRelevance()
{
  d_computed = true;
  Trace("rel-manager") << "RelevanceManager::computeRelevance..." << std::endl;
  std::unordered_map<TNode, int, TNodeHashFunction> cache;
  for (const Node& node: d_input)
  {
    TNode n = node;
    int val = justify(n, cache);
    if (val != 1)
    {
      std::stringstream serr;
      serr << "RelevanceManager::computeRelevance: WARNING: failed to justify "
           << n;
      Trace("rel-manager") << serr.str() << std::endl;
      Assert(false) << serr.str();
      d_success = false;
      return;
    }
  }
  Trace("rel-manager") << "...success, size = " << d_rset.size() << std::endl;
  d_success = true;
}

bool RelevanceManager::isBooleanConnective(TNode cur)
{
  Kind k = cur.getKind();
  return k == NOT || k == IMPLIES || k == AND || k == OR || k == ITE || k == XOR
         || (k == EQUAL && cur[0].getType().isBoolean());
}

bool RelevanceManager::updateJustifyLastChild(
    TNode cur,
    std::vector<int>& childrenJustify,
    std::unordered_map<TNode, int, TNodeHashFunction>& cache)
{
  // This method is run when we are informed that child index of cur
  // has justify status lastChildJustify. We return true if we would like to
  // compute the next child, in this case we push the status of the current
  // child to childrenJustify.
  size_t nchildren = cur.getNumChildren();
  Assert(isBooleanConnective(cur));
  size_t index = childrenJustify.size();
  Assert(index < nchildren);
  Assert(cache.find(cur[index]) != cache.end());
  Kind k = cur.getKind();
  // Lookup the last child's value in the overall cache, we may choose to
  // add this to childrenJustify if we return true.
  int lastChildJustify = cache[cur[index]];
  if (k == NOT)
  {
    cache[cur] = -lastChildJustify;
  }
  else if (k == IMPLIES || k == AND || k == OR)
  {
    if (lastChildJustify != 0)
    {
      // See if we short circuited? The value for short circuiting is false if
      // we are AND or the first child of IMPLIES.
      if (lastChildJustify
          == ((k == AND || (k == IMPLIES && index == 0)) ? -1 : 1))
      {
        cache[cur] = k == AND ? -1 : 1;
        return false;
      }
    }
    if (index + 1 == nchildren)
    {
      // finished all children, compute the overall value
      int ret = k == AND ? 1 : -1;
      for (int cv : childrenJustify)
      {
        if (cv == 0)
        {
          ret = 0;
          break;
        }
      }
      cache[cur] = ret;
    }
    else
    {
      // continue
      childrenJustify.push_back(lastChildJustify);
      return true;
    }
  }
  else if (lastChildJustify == 0)
  {
    // all other cases, an unknown child implies we are unknown
    cache[cur] = 0;
  }
  else if (k == ITE)
  {
    if (index == 0)
    {
      Assert(lastChildJustify != 0);
      // continue with branch
      childrenJustify.push_back(lastChildJustify);
      if (lastChildJustify == -1)
      {
        // also mark first branch as don't care
        childrenJustify.push_back(0);
      }
      return true;
    }
    else
    {
      // should be in proper branch
      Assert(childrenJustify[0] == (index == 1 ? 1 : -1));
      // we are the value of the branch
      cache[cur] = lastChildJustify;
    }
  }
  else
  {
    Assert(k == XOR || k == EQUAL);
    Assert(nchildren == 2);
    Assert(lastChildJustify != 0);
    if (index == 0)
    {
      // must compute the other child
      childrenJustify.push_back(lastChildJustify);
      return true;
    }
    else
    {
      // both children known, compute value
      Assert(childrenJustify.size() == 1 && childrenJustify[0] != 0);
      cache[cur] =
          ((k == XOR ? -1 : 1) * lastChildJustify == childrenJustify[0]) ? 1
                                                                         : -1;
    }
  }
  return false;
}

int RelevanceManager::justify(
    TNode n, std::unordered_map<TNode, int, TNodeHashFunction>& cache)
{
  // the vector of values of children
  std::unordered_map<TNode, std::vector<int>, TNodeHashFunction> childJustify;
  std::unordered_map<TNode, int, TNodeHashFunction>::iterator it;
  std::unordered_map<TNode, std::vector<int>, TNodeHashFunction>::iterator itc;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    // should always have Boolean type
    Assert(cur.getType().isBoolean());
    it = cache.find(cur);
    if (it != cache.end())
    {
      visit.pop_back();
      // already computed value
      continue;
    }
    itc = childJustify.find(cur);
    // have we traversed to children yet?
    if (itc == childJustify.end())
    {
      // are we not a Boolean connective (including NOT)?
      if (isBooleanConnective(cur))
      {
        // initialize its children justify vector as empty
        childJustify[cur].clear();
        // start with the first child
        visit.push_back(cur[0]);
      }
      else
      {
        visit.pop_back();
        // The atom case, lookup the value in the valuation class to
        // see its current value in the SAT solver, if it has one.
        int ret = 0;
        // otherwise we look up the value
        bool value;
        if (d_val.hasSatValue(cur, value))
        {
          ret = value ? 1 : -1;
          d_rset.insert(cur);
        }
        cache[cur] = ret;
      }
    }
    else
    {
      // this processes the impact of the current child on the value of cur,
      // and possibly requests that a new child is computed.
      if (updateJustifyLastChild(cur, itc->second, cache))
      {
        Assert(itc->second.size() < cur.getNumChildren());
        TNode nextChild = cur[itc->second.size()];
        visit.push_back(nextChild);
      }
      else
      {
        visit.pop_back();
      }
    }
  } while (!visit.empty());
  Assert(cache.find(n) != cache.end());
  return cache[n];
}

bool RelevanceManager::isRelevant(Node lit)
{
  if (!d_computed)
  {
    computeRelevance();
  }
  if (!d_success)
  {
    // always relevant if we failed to compute
    return true;
  }
  // agnostic to negation
  while (lit.getKind() == NOT)
  {
    lit = lit[0];
  }
  return d_rset.find(lit) != d_rset.end();
}

}  // namespace theory
}  // namespace CVC4
