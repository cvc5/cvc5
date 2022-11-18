/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Propagation finder
 */

#include "decision/prop_finder.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::prop;

namespace cvc5::internal {
namespace decision {

PropFindInfo::PropFindInfo(context::Context* c)
    : d_childIndex(c, 0), d_parentList(c)
{
}

PropFinder::PropFinder(Env& env,
                       prop::CDCLTSatSolverInterface* ss,
                       prop::CnfStream* cs)
    : EnvObj(env), d_pstate(context()), d_jcache(context(), ss, cs)
{
}

PropFinder::~PropFinder() {}

void PropFinder::addAssertion(TNode n,
                              TNode skolem,
                              bool isLemma,
                              std::vector<TNode>& toPreregister)
{
  if (!skolem.isNull())
  {
    // skolem definitions handled dynamically
    return;
  }
  updateRelevant(n, toPreregister);
}

void PropFinder::notifyActiveSkolemDefs(std::vector<TNode>& defs,
                                        std::vector<TNode>& toPreregister)
{
  for (TNode d : defs)
  {
    updateRelevant(d, toPreregister);
  }
}

void PropFinder::updateRelevant(TNode n, std::vector<TNode>& toPreregister)
{
  bool pol = n.getKind() != kind::NOT;
  TNode natom = pol ? n : n[0];
  if (d_jcache.hasValue(natom))
  {
    // already justified, we are done
    return;
  }
  updateRelevantInternal(
      natom, pol ? SAT_VALUE_TRUE : SAT_VALUE_FALSE, toPreregister);
}

void PropFinder::updateRelevantInternal(TNode n,
                                        prop::SatValue val,
                                        std::vector<TNode>& toPreregister)
{
  // (child, desired polarity), parent
  std::vector<std::pair<JustifyNode, TNode> > toVisit;
  toVisit.emplace_back(JustifyNode(n, val), d_null);
  std::pair<JustifyNode, TNode> t;
  context::CDInsertHashMap<Node, std::shared_ptr<PropFindInfo> >::const_iterator
      it;
  TNode curr;
  prop::SatValue currVal;
  TNode parent;
  Kind ck;
  do
  {
    t = toVisit.back();
    toVisit.pop_back();
    curr = t.first.first;
    currVal = t.first.second;
    parent = t.second;
    ck = curr.getKind();
    Assert(ck != kind::NOT);
    Assert(curr.getType().isBoolean());
    it = d_pstate.find(curr);
    // impact of looking at current node: the value we computed, and which
    // children we should watch.
    prop::SatValue jval = SAT_VALUE_UNKNOWN;
    std::vector<JustifyNode> watchChildren;
    if (ck == AND || ck == OR)
    {
      bool childValForce = ((ck == AND) == (currVal == SAT_VALUE_FALSE));
      // see if already justified?
      for (TNode c : curr)
      {
        bool cpol = c.getKind() != AND;
        TNode catom = cpol ? c : c[0];
        prop::SatValue cval = d_jcache.lookupValue(c);
        if (cval == SAT_VALUE_UNKNOWN)
        {
          // watch all children if child value is forcing
          if (childValForce || watchChildren.empty())
          {
            watchChildren.emplace_back(catom,
                                       cpol ? currVal : invertValue(currVal));
          }
        }
        else if (childValForce && cval != currVal)
        {
          // value is forced
          jval = currVal;
          break;
        }
      }
    }
    else if (ck == IMPLIES)
    {
    }
    else if (ck == ITE)
    {
    }
    else if (ck == EQUAL || ck == XOR)
    {
    }
    else
    {
      // its a theory atom, preregister it
      toPreregister.push_back(curr);
    }
    if (jval != SAT_VALUE_UNKNOWN)
    {
      // value is forced
      d_jcache.setValue(curr, jval);
      // notify parents?
    }
    else
    {
      // process watch children
      for (const JustifyNode& wc : watchChildren)
      {
        toVisit.emplace_back(wc, curr);
      }
    }
  } while (!toVisit.empty());
}

void PropFinder::notifyAsserted(TNode n, std::vector<TNode>& toPreregister)
{
  bool pol = n.getKind() != kind::NOT;
  TNode natom = pol ? n : n[0];
  // set justified
  d_jcache.setValue(natom, pol ? SAT_VALUE_TRUE : SAT_VALUE_FALSE);
  // update relevance on parents, if any
  context::CDInsertHashMap<Node, std::shared_ptr<PropFindInfo> >::const_iterator
      it = d_pstate.find(natom);
  if (it != d_pstate.end())
  {
    for (const JustifyNode& p : it->second->d_parentList)
    {
      updateRelevantInternal(p.first, p.second, toPreregister);
    }
  }
  /*
    // then, visit parents recursively
    // node, assigned value
    std::vector<TNode> toVisit;
    toVisit.emplace_back(natom);
    context::CDInsertHashMap<Node, std::shared_ptr<PropFindInfo>
    >::const_iterator it; TNode curr; Kind ck; do
    {
      curr = toVisit.back();
      toVisit.pop_back();
      d_pstate.find(curr);
      if (d_pstate.find(curr) == d_pstate.end())
      {
        // not watching it
        continue;
      }
      ck = curr.getKind();
      Assert(ck != kind::NOT);
      if (ck == AND || ck == OR)
      {
        if ((ck == AND) == (currVal == SAT_VALUE_FALSE))
        {
        }
        else
        {
        }
      }
      else if (ck == IMPLIES)
      {
      }
      else if (ck == ITE)
      {
      }
      else if (ck == EQUAL || ck == XOR)
      {
      }

    } while (!toVisit.empty());
  */
}

PropFindInfo* PropFinder::getOrMkInfo(TNode n) { return nullptr; }

}  // namespace decision
}  // namespace cvc5::internal
