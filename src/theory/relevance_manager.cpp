/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of relevance manager.
 */

#include "theory/relevance_manager.h"

#include <sstream>

#include "options/smt_options.h"
#include "smt/env.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {

RelevanceManager::RelevanceManager(Env& env, Valuation val)
    : EnvObj(env),
      d_val(val),
      d_input(userContext()),
      d_rset(context()),
      d_inFullEffortCheck(false),
      d_success(false),
      d_trackRSetExp(false),
      d_miniscopeTopLevel(true),
      d_rsetExp(context()),
      d_jcache(context())
{
  if (options().smt.produceDifficulty)
  {
    d_dman.reset(new DifficultyManager(userContext(), val));
    d_trackRSetExp = true;
    // we cannot miniscope AND at the top level, since we need to
    // preserve the exact form of preprocessed assertions so the dependencies
    // are tracked.
    d_miniscopeTopLevel = false;
  }
}

void RelevanceManager::notifyPreprocessedAssertions(
    const std::vector<Node>& assertions, bool isInput)
{
  // add to input list, which is user-context dependent
  std::vector<Node> toProcess;
  for (const Node& a : assertions)
  {
    if (d_miniscopeTopLevel && a.getKind() == AND)
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
  // notify the difficulty manager if these are input assertions
  if (isInput && d_dman != nullptr)
  {
    d_dman->notifyInputAssertions(assertions);
  }
}

void RelevanceManager::notifyPreprocessedAssertion(Node n, bool isInput)
{
  std::vector<Node> toProcess;
  toProcess.push_back(n);
  notifyPreprocessedAssertions(toProcess, isInput);
}

void RelevanceManager::addAssertionsInternal(std::vector<Node>& toProcess)
{
  size_t i = 0;
  while (i < toProcess.size())
  {
    Node a = toProcess[i];
    if (d_miniscopeTopLevel && a.getKind() == AND)
    {
      // difficulty tracking disables miniscoping of AND
      Assert(d_dman == nullptr);
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

void RelevanceManager::beginRound() { d_inFullEffortCheck = true; }

void RelevanceManager::endRound() { d_inFullEffortCheck = false; }

void RelevanceManager::computeRelevance()
{
  // if not at full effort, should be tracking something else, e.g. explanation
  // for why literals are relevant.
  Assert(d_inFullEffortCheck || d_trackRSetExp);
  Trace("rel-manager") << "RelevanceManager::computeRelevance, full effort = "
                       << d_inFullEffortCheck << "..." << std::endl;
  for (const Node& node: d_input)
  {
    TNode n = node;
    int val = justify(n);
    if (val != 1)
    {
      // if we are in full effort check and fail to justify, then we should
      // give a failure and set success to false, or otherwise calls to
      // isRelevant cannot be trusted.
      if (d_inFullEffortCheck)
      {
        std::stringstream serr;
        serr
            << "RelevanceManager::computeRelevance: WARNING: failed to justify "
            << n;
        Trace("rel-manager") << serr.str() << std::endl;
        Assert(false) << serr.str();
        d_success = false;
        return;
      }
    }
  }
  if (Trace.isOn("rel-manager"))
  {
    if (d_inFullEffortCheck)
    {
      Trace("rel-manager") << "...success (full), size = " << d_rset.size()
                           << std::endl;
    }
    else
    {
      Trace("rel-manager") << "...success, exp size = " << d_rsetExp.size()
                           << std::endl;
    }
  }
  d_success = true;
}

bool RelevanceManager::isBooleanConnective(TNode cur)
{
  Kind k = cur.getKind();
  return k == NOT || k == IMPLIES || k == AND || k == OR || k == ITE || k == XOR
         || (k == EQUAL && cur[0].getType().isBoolean());
}

bool RelevanceManager::updateJustifyLastChild(TNode cur,
                                              std::vector<int>& childrenJustify)
{
  // This method is run when we are informed that child index of cur
  // has justify status lastChildJustify. We return true if we would like to
  // compute the next child, in this case we push the status of the current
  // child to childrenJustify.
  size_t nchildren = cur.getNumChildren();
  Assert(isBooleanConnective(cur));
  size_t index = childrenJustify.size();
  Assert(index < nchildren);
  Assert(d_jcache.find(cur[index]) != d_jcache.end());
  Kind k = cur.getKind();
  // Lookup the last child's value in the overall cache, we may choose to
  // add this to childrenJustify if we return true.
  int lastChildJustify = d_jcache[cur[index]];
  if (k == NOT)
  {
    d_jcache[cur] = -lastChildJustify;
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
        d_jcache[cur] = k == AND ? -1 : 1;
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
      d_jcache[cur] = ret;
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
    d_jcache[cur] = 0;
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
      d_jcache[cur] = lastChildJustify;
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
      d_jcache[cur] =
          ((k == XOR ? -1 : 1) * lastChildJustify == childrenJustify[0]) ? 1
                                                                         : -1;
    }
  }
  return false;
}

int RelevanceManager::justify(TNode n)
{
  // The set of nodes that we have computed currently have no value. Those
  // that are marked as having no value in d_jcache must be recomputed, since
  // the values for SAT literals may have changed.
  std::unordered_set<Node> noJustify;
  // the vector of values of children
  std::unordered_map<TNode, std::vector<int>> childJustify;
  NodeUIntMap::iterator it;
  std::unordered_map<TNode, std::vector<int>>::iterator itc;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    // should always have Boolean type
    Assert(cur.getType().isBoolean());
    it = d_jcache.find(cur);
    if (it != d_jcache.end())
    {
      if (it->second != 0 || noJustify.find(cur) != noJustify.end())
      {
        visit.pop_back();
        // already computed value
        continue;
      }
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
          if (d_trackRSetExp)
          {
            d_rsetExp[cur] = n;
            Trace("rel-manager-exp")
                << "Reason for " << cur << " is " << n << std::endl;
          }
        }
        d_jcache[cur] = ret;
        if (ret == 0)
        {
          noJustify.insert(cur);
        }
      }
    }
    else
    {
      // this processes the impact of the current child on the value of cur,
      // and possibly requests that a new child is computed.
      if (updateJustifyLastChild(cur, itc->second))
      {
        Assert(itc->second.size() < cur.getNumChildren());
        TNode nextChild = cur[itc->second.size()];
        visit.push_back(nextChild);
      }
      else
      {
        visit.pop_back();
        Assert(d_jcache.find(cur) != d_jcache.end());
        if (d_jcache[cur] == 0)
        {
          noJustify.insert(cur);
        }
      }
    }
  } while (!visit.empty());
  Assert(d_jcache.find(n) != d_jcache.end());
  return d_jcache[n];
}

bool RelevanceManager::isRelevant(Node lit)
{
  Assert(d_inFullEffortCheck);
  computeRelevance();
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

std::unordered_set<TNode> RelevanceManager::getRelevantAssertions(bool& success)
{
  computeRelevance();
  // update success flag
  success = d_success;
  std::unordered_set<TNode> rset;
  if (success)
  {
    for (const Node& a : d_rset)
    {
      rset.insert(a);
    }
  }
  return rset;
}

void RelevanceManager::notifyLemma(Node n)
{
  // notice that we may be in FULL or STANDARD effort here.
  if (d_dman != nullptr)
  {
    // ensure we know which literals are relevant, and why
    computeRelevance();
    d_dman->notifyLemma(d_rsetExp, n);
  }
}

void RelevanceManager::notifyCandidateModel(TheoryModel* m)
{
  if (d_dman != nullptr)
  {
    d_dman->notifyCandidateModel(m);
  }
}

void RelevanceManager::getDifficultyMap(std::map<Node, Node>& dmap)
{
  if (d_dman != nullptr)
  {
    d_dman->getDifficultyMap(dmap);
  }
}

}  // namespace theory
}  // namespace cvc5
