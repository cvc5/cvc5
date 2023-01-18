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
    : d_rvalProcessed(c, false),
      d_rval(c, SAT_VALUE_UNKNOWN),
      d_childIndex(c, 0),
      d_parentList(c)
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
  // set relevant
  markRelevant(natom, pol ? SAT_VALUE_TRUE : SAT_VALUE_FALSE);
  // update the relevance
  std::vector<std::pair<TNode, bool>> justifyQueue;
  updateRelevantInternal(natom, toPreregister);
}

/*

- Is it worthwhile to cache index?

- Invariants:
  - If become justified, then we have called updateRelevantInternal on entire parent list.
  - for 0...d_childIndex-1, all child of AND/OR are justified with non-forcing value
*/



// NOTE: responsible for popping self from toVisit!!!!
prop::SatValue PropFinder::updateRelevantInternal2(TNode n,
                                                   std::vector<TNode>& toPreregister,
                                                   std::vector<TNode>& toVisit)
{
  Assert (n.getKind()!=NOT);
  PropFindInfo* currInfo = getInfo(n);
  Assert (currInfo!=nullptr);
  // if we've processed relevance, we are done
  if (currInfo->d_rvalProcessed.get())
  {
    toVisit.pop_back();
    return SAT_VALUE_UNKNOWN;
  }
  // if we've justified, we should have marked that we are done
  Assert (!d_jcache.hasValue(n));
  Kind nk = n.getKind();
  // the current relevance value we are processing
  prop::SatValue rval = currInfo->d_rval;
  // if the justified value of n is found in this call, this is set to its value
  prop::SatValue newJval = SAT_VALUE_UNKNOWN;
  size_t cindex = currInfo->d_childIndex;
  Assert (cindex<=n.getNumChildren());
  if (nk == AND || nk == OR || nk == IMPLIES)
  {
    prop::SatValue forceVal = (nk == AND) ? SAT_VALUE_FALSE : SAT_VALUE_TRUE;
    bool invertChild = (nk == IMPLIES && cindex==0);
    // check the status of the last child we looked at, if it exists
    if (cindex>0)
    {
      TNode prevChild = n[cindex-1];
      prop::SatValue cval = d_jcache.lookupValue(prevChild);
      cval = invertChild ? invertValue(cval) : cval;
      // if it did not have a value
      if (cval == SAT_VALUE_UNKNOWN)
      {
        bool watchAll = rval==SAT_VALUE_UNKNOWN || ((nk == AND) == (rval == SAT_VALUE_FALSE));
        // if we found an unknown child and aren't watching all children, we are done for now
        if (!watchAll)
        {
          // TODO: mark watch from prevChild to this
          currInfo->d_rvalProcessed = true;
          toVisit.pop_back();
          return SAT_VALUE_UNKNOWN;
        }
      }
      else if (cval==forceVal)
      {
        // if the child's value forces this, we are done
        toVisit.pop_back();
        newJval = forceVal;
      }
    }
    // if we didn't justify above, then look at the next child
    if (newJval==SAT_VALUE_UNKNOWN)
    {
      if (cindex==n.getNumChildren())
      {
        // We didn't find a child to watch, this means we are in the exhausted
        // case. We set our value to the inverted forced value.
        toVisit.pop_back();
        newJval = invertValue(forceVal);
      }
      else
      {
        // Otherwise, set the next child to relevant and add toVisit. We
        // will visit the current term again when we are finished.
        TNode nextChild = n[cindex];
        if (nextChild.getKind()==NOT)
        {
          nextChild =  nextChild[0];
          invertChild = !invertChild;
        }
        // the relevance value of the child is based on the relevance value of
        // this, possibly inverted in nextChild was negated or is the first
        // child of IMPLIES.
        prop::SatValue crval = invertChild ? invertValue(rval) : rval;
        markRelevant(nextChild, crval);
        toVisit.emplace_back(nextChild);
        currInfo->d_childIndex = cindex + 1;
      }
    }
  }
  else if (nk == ITE || nk == EQUAL || nk == XOR)
  {
    Assert (cindex<=n.getNumChildren());
    if (cindex==0)
    {
      // watch the first child with unknown polarity
      markRelevant(n[0], SAT_VALUE_UNKNOWN);
      toVisit.emplace_back(n[0]);
      currInfo->d_childIndex = cindex + 1;
    }
    else
    {
      // check the value of last child
      prop::SatValue cval = d_jcache.lookupValue(n[cindex-1]);
      if (cval==SAT_VALUE_UNKNOWN)
      {
        // value is unknown, we are done for now
        // TODO: mark watch from n[cindex-1] to this
        currInfo->d_rvalProcessed = true;
        toVisit.pop_back();
        return SAT_VALUE_UNKNOWN;
      }
      else if (cindex==1)
      {
        // set the child index to the index of relevant child + 1
        // visit the relevant child
        size_t rcindex = (nk!=ITE || cval==SAT_VALUE_TRUE) ? 2 : 3;
        TNode nextChild = n[rcindex-1];
        markRelevant(nextChild, rval);
        toVisit.emplace_back(nextChild);
        currInfo->d_childIndex = rcindex;
      }
      else
      {
        toVisit.pop_back();
        if (nk==ITE)
        {
          // the value of this is the value of the branch
          newJval = cval;
        }
        else
        {
          // recompute the first child and compute the result
          prop::SatValue cval0 = d_jcache.lookupValue(n[0]);
          Assert (cval0!=SAT_VALUE_UNKNOWN);
          newJval = (nk==XOR ? cval!=cval0 : cval==cval0) ? SAT_VALUE_TRUE : SAT_VALUE_FALSE;
        }
      }
    }
  }
  else
  {
    // theory literals are added to the preregister queue
    toVisit.pop_back();
    currInfo->d_rvalProcessed = true;
    toPreregister.push_back(n);
  }
  return newJval;
}

void PropFinder::markRelevant(TNode n, prop::SatValue val)
{
  if (n.getKind()==NOT)
  {
    n = n[0];
    val = invertValue(val);
  }
  Assert (n.getKind()!=NOT);
  // if we already have a value, don't bother
  if (d_jcache.hasValue(n))
  {
    return;
  }
  // Otherwise, take the union of relevant values. If we update our relevant
  // values, then we require processing relevance again.
  PropFindInfo* currInfo = getOrMkInfo(n);
  prop::SatValue prevVal = currInfo->d_rval;
  prop::SatValue newVal = relevantUnion(val, prevVal);
  if (newVal!=prevVal)
  {
    // update relevance value and reset counters
    currInfo->d_rval = newVal;
    currInfo->d_childIndex = 0;
    currInfo->d_rvalProcessed = false;
  }
}

void PropFinder::updateRelevantInternal(TNode n,
                                        std::vector<TNode>& toPreregister)
{
  Assert (n.getKind()!=NOT);
  // The nodes we discovered the justification for during this call.
  std::vector<TNode> justified;
  // (child, desired polarity), parent. We forbid NOT for child and parent.
  std::vector<TNode> toVisit;
  toVisit.emplace_back(n);
  TNode t;
  do
  {
    t = toVisit.back();
    // update relevant
    prop::SatValue jval = updateRelevantInternal2(t, toPreregister, toVisit);
    // if we found it was justified
    if (jval!=SAT_VALUE_UNKNOWN)
    {
      // set its value in the justification cache
      d_jcache.setValue(t, jval);
      // add it to the queue for notifications
      justified.emplace_back(t);
    }
  } while (!toVisit.empty());
  
  // process justification / parent notifies
  for (TNode jn : justified)
  {
    notifyWatchParents(jn);
  }
}

void PropFinder::notifyAsserted(TNode n, std::vector<TNode>& toPreregister)
{
  bool pol = n.getKind() != kind::NOT;
  TNode natom = pol ? n : n[0];
  d_jcache.setValue(natom, pol ? SAT_VALUE_TRUE : SAT_VALUE_FALSE);
  // set justified
  notifyWatchParents(natom);
}

void PropFinder::notifyWatchParents(TNode n)
{
}

PropFindInfo* PropFinder::getInfo(TNode n)
{
  context::CDInsertHashMap<Node, std::shared_ptr<PropFindInfo> >::const_iterator
      it = d_pstate.find(n);
  if (it != d_pstate.end())
  {
    return it->second.get();
  }
  return nullptr;
}

PropFindInfo* PropFinder::mkInfo(TNode n)
{
  Assert(d_pstate.find(n) == d_pstate.end());
  std::shared_ptr<PropFindInfo> pi = std::make_shared<PropFindInfo>(context());
  d_pstate.insert(n, pi);
  return pi.get();
}

PropFindInfo* PropFinder::getOrMkInfo(TNode n)
{
  PropFindInfo* pi = getInfo(n);
  if (pi != nullptr)
  {
    return pi;
  }
  return mkInfo(n);
}

prop::SatValue PropFinder::relevantUnion(prop::SatValue r1, prop::SatValue r2)
{
  return r1 == r2 ? r1 : SAT_VALUE_UNKNOWN;
}

}  // namespace decision
}  // namespace cvc5::internal
