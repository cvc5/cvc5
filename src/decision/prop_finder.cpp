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
    : d_rval(c, SAT_VALUE_UNKNOWN), d_jval(c, SAT_VALUE_UNKNOWN), d_childIndex(c, 0), d_parentList(c)
{
}

bool PropFindInfo::hasJustified() const
{
  return d_jval.get()!=SAT_VALUE_UNKNOWN;
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
/*

- Is it worthwhile to cache index?


- Invariant:
If become justified, then we have called updateRelevantInternal
on entire parent list.

for 0...d_childIndex-1, all child of AND/OR are justified with non-forcing value
*/

void PropFinder::updateRelevantInternal(TNode n,
                                        prop::SatValue val,
                                        std::vector<TNode>& toPreregister)
{
#if 0
  std::vector<std::pair<TNode, bool>> queueNotifyParent;
  // (child, desired polarity), parent
  // NOTE: we only push downwards in this method
  std::vector<std::pair<JustifyNode, TNode> > toVisit;
  toVisit.emplace_back(JustifyNode(n, val), d_null);
  std::pair<JustifyNode, TNode> t;
  context::CDInsertHashMap<Node, std::shared_ptr<PropFindInfo> >::const_iterator
      it;
  TNode curr;
  bool currPol;
  prop::SatValue currRVal;
  TNode parent;
  Kind ck;
  PropFindInfo* currInfo = nullptr;
  do
  {
    t = toVisit.back();
    toVisit.pop_back();
    curr = t.first.first;
    currPol = curr.getKind()!=NOT;
    curr = currPol ? curr : curr[0];
    currRVal = t.first.second;
    parent = t.second;
    ck = curr.getKind();
    // get the info for curr, if it exists
    currInfo = getInfo(curr);
    if (currInfo!=nullptr)
    {
      if (currInfo->hasJustified())
      {
        // the value of this node has already been justified
        continue;
      }
      prevRVal = currInfo->d_rval.get();
      currRVal = relevantUnion(currRVal, prevRVal);
      if (currRVal==prevRVal)
      {
        // we've already marked this node with the given relevance
        continue;
      }
    }
    Assert(ck != kind::NOT);
    Assert(curr.getType().isBoolean());
    // impact of looking at current node: the value we computed, and which
    // children we should watch.
    prop::SatValue jval = SAT_VALUE_UNKNOWN;
    std::vector<std::pair<JustifyNode, TNode>> watchChildren;
    if (ck == AND || ck == OR || ck == IMPLIES)
    {
      // get the index of children we should start looking at
      size_t startIndex = currInfo==nullptr ? 0 : currInfo->d_childIndex.get();
      size_t endIndex = curr.getNumChildren();
      // if we haven't already watched all children
      if (startIndex<endIndex)
      {
        bool watchAll = currRVal==SAT_VALUE_UNKNOWN || ((ck == AND) == (currRVal == SAT_VALUE_FALSE));
        prop::SatValue forceVal = (ck == AND) ? SAT_VALUE_FALSE : SAT_VALUE_TRUE;
        // see if already justified?
        size_t nextIndex = startIndex;
        for (size_t i=startIndex; i<endIndex; i++)
        {
          bool cpol = curr[i].getKind() != AND;
          TNode catom = cpol ? curr[i] : curr[i][0];
          prop::SatValue cval = d_jcache.lookupValue(catom);
          cval = cpol ? cval : invertValue(cval);
          // for each child that doesn't have a justified value
          if (cval == SAT_VALUE_UNKNOWN)
          {
            // watch all children if we are watching all, or watch one otherwise
            if (watchAll || watchChildren.empty())
            {
              prop::SatValue childRVal = (ck==IMPLIES && 
              watchChildren.emplace_back(JustifyNode(curr[i], childRVal), curr);
              nextIndex = i;
            }
          }
          else if (cval == forceVal)
          {
            // value is forced
            jval = cval;
            break;
          }
        }
        if (jval==SAT_VALUE_UNKNOWN)
        {
          if (watchChildren.empty())
          {
            // we didn't find a child to watch, this means we are in the exhausted case
            jval = invertValue(forceVal);
          }
          else
          {
            // otherwise, update the next index
            currInfo->d_childIndex = nextIndex;
          }
        }
      }
    }
    else if (ck == ITE)
    {
      // watch condition, unless it has a value?
    }
    else if (ck == EQUAL || ck == XOR)
    {
      // if first time seeing this, watch both children?
    }
    else
    {
      // its a theory atom, preregister it
      toPreregister.push_back(curr);
      continue;
    }
    if (currInfo==nullptr)
    {
      currInfo = mkInfo(curr);
    }
    currInfo->d_rval = currRVal;
    // process the parent
    if (!parent.isNull())
    {
      
    }
    // if the value was determined on this call
    if (jval != SAT_VALUE_UNKNOWN)
    {
      // value is forced
      d_jcache.setValue(curr, jval);
      currInfo->d_jval = jval;
      // notify parents
      bool pol = (jval==SAT_VALUE_TRUE);
      for (const std::pair<Node, bool>& p : currInfo->d_parentList)
      {
        queueNotifyParent.emplace_back(p.first, p.second ? pol : !pol);
      }
    }
    else
    {
      // visit the watched children
      toVisit.insert(toVisit.end(), watchChildren.begin(), watchChildren.end());
    }
  } while (!toVisit.empty());
  // TODO: process parent notifies
#endif
}

void PropFinder::notifyAsserted(TNode n, std::vector<TNode>& toPreregister)
{
#if 0
  bool pol = n.getKind() != kind::NOT;
  TNode natom = pol ? n : n[0];
  // set justified
  d_jcache.setValue(natom, pol ? SAT_VALUE_TRUE : SAT_VALUE_FALSE);
  // update relevance on parents, if any
  context::CDInsertHashMap<Node, std::shared_ptr<PropFindInfo> >::const_iterator
      it;
  // notify the parents
  it = d_pstate.find(natom);
  if (it != d_pstate.end())
  {
    for (const std::pair<Node, bool>& p : it->second->d_parentList)
    {
      notifyParentInternal(p.first, p.second ? pol : !pol);
    }
  }
#endif
}


// TODO: queue is argument?
void PropFinder::notifyParentInternal(TNode n, bool childVal)
{
#if 0
  std::vector<std::pair<TNode, prop::SatValue>> queueUpdateRelevant;
  // notify values: node to notify, child's value
  // this method only pushes upwards to parents
  std::vector<std::pair<TNode, bool>> toNotify;
  toNotify.emplace_back(n, childVal);
  std::pair<TNode, bool> t;
  TNode curr;
  bool currChildVal;
  PropFindInfo* currInfo = nullptr;
  while (!toNotify.empty())
  {
    t = toNotify.back();
    toNotify.pop_back();
    curr = t.first;
    currInfo = getInfo(curr);
    // all parents have allocated infos
    Assert (currInfo!=nullptr);
    if (currInfo->hasJustified())
    {
      continue;
    }
    currChildVal = t.second;
    // see if we justify now
    prop::SatValue jval = SAT_VALUE_UNKNOWN;
    if (ck == AND || ck == OR)
    {
      // TODO: watch and then evaluate? or go to next child
      bool forceVal = (ck == AND) ? false : true;
      if (currChildVal==forceVal)
      {
        // value is forced
        jval = forceVal ? SAT_VALUE_TRUE : SAT_VALUE_FALSE;
      }
      else
      {
        // update relevant
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
      // TODO: watch and then evaluate?
    }
    else
    {
      Assert(false);
    }
    // TODO: justify is now set
    if (jval != SAT_VALUE_UNKNOWN)
    {
      d_jcache.setValue(curr, jval);
      // notify parents
    }
  }
#endif
}

PropFindInfo* PropFinder::getInfo(TNode n)
{
  context::CDInsertHashMap<Node, std::shared_ptr<PropFindInfo> >::const_iterator it = d_pstate.find(n);
  if (it != d_pstate.end())
  {
    return it->second.get();
  }
  return nullptr;
}

PropFindInfo* PropFinder::mkInfo(TNode n)
{
  Assert (d_pstate.find(n)==d_pstate.end());
  std::shared_ptr<PropFindInfo> pi = std::make_shared<PropFindInfo>(context());
  d_pstate.insert(n, pi);
  return pi.get();
}

PropFindInfo* PropFinder::getOrMkInfo(TNode n)
{ 
  PropFindInfo* pi = getInfo(n);
  if (pi!=nullptr)
  {
    return pi;
  }
  return mkInfo(n);
}

prop::SatValue PropFinder::relevantUnion(prop::SatValue r1, prop::SatValue r2)
{
  return r1==r2 ? r1 : SAT_VALUE_UNKNOWN;
}

}  // namespace decision
}  // namespace cvc5::internal
