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
    : d_iter(c, 0),
      d_rval(c, SAT_VALUE_UNKNOWN),
      d_childIndex(c, 0),
      d_parentList(c)
{
}

PropFinder::PropFinder(Env& env,
                       CDCLTSatSolverInterface* ss,
                       CnfStream* cs)
    : EnvObj(env),
      d_pstate(context()),
      d_assertions(userContext()),
      d_assertionIndex(context(), 0),
      d_jcache(context(), ss, cs),
      d_statSatPrereg(context(), 0),
      d_statPrereg(context(), 0)

{
}

PropFinder::~PropFinder() {}

void PropFinder::check(std::vector<TNode>& toPreregister)
{
  // ensure that all assertions have been marked as relevant
  size_t asize = d_assertions.size();
  while (d_assertionIndex.get() < asize)
  {
    TNode n = d_assertions[d_assertionIndex];
    updateRelevant(n, toPreregister);
    d_assertionIndex = d_assertionIndex + 1;
  }
}

void PropFinder::addAssertion(TNode n, TNode skolem, bool isLemma)
{
  if (!skolem.isNull())
  {
    // skolem definitions handled dynamically
    return;
  }
  // buffer it into the list of assertions
  Trace("prop-finder") << "PropFinder: add assertion " << n << std::endl;
  d_assertions.push_back(n);
}

void PropFinder::notifySatLiteral(TNode n)
{
  Trace("prop-finder") << "PropFinder: notify SAT literal " << n << std::endl;
  // do nothing, only for stats
  d_statSatPrereg = d_statSatPrereg + 1;
}

void PropFinder::notifyActiveSkolemDefs(std::vector<TNode>& defs,
                                        std::vector<TNode>& toPreregister)
{
  for (TNode d : defs)
  {
    Trace("prop-finder") << "PropFinder: add skolem definition " << d
                         << std::endl;
    updateRelevant(d, toPreregister);
  }
}

void PropFinder::notifyAsserted(TNode n, std::vector<TNode>& toPreregister)
{
  Trace("prop-finder") << "PropFinder: notify asserted " << n << std::endl;
  bool pol = n.getKind() != kind::NOT;
  TNode natom = pol ? n : n[0];
  // update relevant, which will ensure that natom is preregistered if not
  // already done so
  updateRelevant(natom, toPreregister);
  // we don't set justified explicitly here, instead the parent(s) will query
  // the value of n
  std::vector<std::pair<TNode, SatValue>> justifyQueue;
  justifyQueue.emplace_back(natom, pol ? SAT_VALUE_TRUE : SAT_VALUE_FALSE);
  std::vector<TNode> toVisit;
  updateJustify(justifyQueue, toVisit);
  Trace("prop-finder-debug2")
      << "...will visit " << toVisit.size() << " parents" << std::endl;
  updateRelevantInternal(toVisit, toPreregister);
}

void PropFinder::updateRelevant(TNode n, std::vector<TNode>& toPreregister)
{
  bool pol = n.getKind() != kind::NOT;
  TNode nn = pol ? n : n[0];
  if (d_jcache.hasValue(nn))
  {
    // already justified, we are done
    return;
  }
  // mark that the formula is relevant with its asserted polarity
  std::vector<TNode> toVisit;
  markRelevant(nn, pol ? SAT_VALUE_TRUE : SAT_VALUE_FALSE, toVisit);
  // process its relevance
  updateRelevantInternal(toVisit, toPreregister);
}

void PropFinder::updateRelevantInternal(std::vector<TNode>& toVisit,
                                        std::vector<TNode>& toPreregister)
{
  // (child, desired polarity), parent. We forbid NOT for child and parent.
  std::vector<std::pair<TNode, SatValue>> justifyQueue;
  TNode t;
  while (!toVisit.empty())
  {
    t = toVisit.back();
    Assert(t.getKind() != NOT);
    // update relevant
    SatValue jval = updateRelevantInternal2(t, toPreregister, toVisit);
    // if we found it was justified
    if (jval != SAT_VALUE_UNKNOWN)
    {
      Trace("prop-finder-debug")
          << "Mark " << t << " as justified " << jval << std::endl;
      // set its value in the justification cache
      d_jcache.setValue(t, jval);
      // add it to the queue for notifications
      justifyQueue.emplace_back(t, jval);
    }
    // If we are done visiting, process the justify queue, which will
    // add parents to visit
    if (toVisit.empty())
    {
      updateJustify(justifyQueue, toVisit);
      justifyQueue.clear();
    }
  }
}

bool shouldWatchAll(Kind nk, SatValue rval)
{
  return rval != SAT_VALUE_UNKNOWN && ((nk == AND) == (rval == SAT_VALUE_TRUE));
}

// NOTE: responsible for popping self from toVisit!!!!
SatValue PropFinder::updateRelevantInternal2(
    TNode n, std::vector<TNode>& toPreregister, std::vector<TNode>& toVisit)
{
  Trace("prop-finder-debug2") << "Update relevance on " << n << std::endl;
  Assert(n.getKind() != NOT);
  PropFindInfo* currInfo = getInfo(n);
  // we should have already been marked relevant
  Assert(currInfo != nullptr);
  // if we've processed relevance, we are done
  /*
  if (!currInfo->isActive())
  {
    Trace("prop-finder-debug2") << "...already processed" << std::endl;
    toVisit.pop_back();
    return SAT_VALUE_UNKNOWN;
  }
  */
  // if we've justified already
  if (d_jcache.hasValue(n))
  {
    Trace("prop-finder-debug2") << "...already justified" << std::endl;
    toVisit.pop_back();
    return SAT_VALUE_UNKNOWN;
  }
  Kind nk = n.getKind();
  // the current relevance value we are processing
  SatValue rval = currInfo->d_rval;
  // if the justified value of n is found in this call, this is set to its value
  SatValue newJval = SAT_VALUE_UNKNOWN;
  size_t cindex = currInfo->d_childIndex;
  Trace("prop-finder-debug2")
      << "...relevance " << rval << ", childIndex " << cindex << ", iteration "
      << currInfo->d_iter << std::endl;
  Assert(cindex <= n.getNumChildren());
  if (nk == AND || nk == OR || nk == IMPLIES)
  {
    SatValue forceVal = (nk == AND) ? SAT_VALUE_FALSE : SAT_VALUE_TRUE;
    bool invertChild = (nk == IMPLIES && cindex == 0);
    size_t iter = currInfo->d_iter;
    // check the status of the last child we looked at, if it exists
    if (cindex > 0)
    {
      TNode prevChild = n[cindex - 1];
      SatValue cval = d_jcache.lookupValue(prevChild);
      cval = invertChild ? invertValue(cval) : cval;
      // if it did not have a value
      if (cval == SAT_VALUE_UNKNOWN)
      {
        // Watch all children if a single value would force us to our relevant
        // value, or if we are in iter=1.
        // If we found an unknown child and aren't watching all children, we are
        // done for now.
        if (iter == 1 || !shouldWatchAll(nk, rval))
        {
          // mark watch from prevChild to this
          markWatchedParent(prevChild, n, invertChild ? SAT_VALUE_FALSE : SAT_VALUE_TRUE);
          toVisit.pop_back();
          return SAT_VALUE_UNKNOWN;
        }
      }
      else if (cval == forceVal)
      {
        // if the child's value forces this, we are done
        toVisit.pop_back();
        newJval = forceVal;
      }
      // otherwise, it contributes to the exhausted case
    }
    // if we didn't justify above, then look at the next child
    if (newJval == SAT_VALUE_UNKNOWN)
    {
      if (cindex == n.getNumChildren())
      {
        if (iter == 1 || !shouldWatchAll(nk, rval))
        {
          // We didn't find a child to watch, this means we are in the exhausted
          // case. We set our value to the inverted forced value.
          toVisit.pop_back();
          newJval = invertValue(forceVal);
        }
        else
        {
          // otherwise, we will do another pass to check for justification
          currInfo->d_iter = iter + 1;
        }
      }
      else
      {
        if (iter == 0)
        {
          // Otherwise, set the next child to relevant and add toVisit. We
          // will visit the current term again when we are finished.
          TNode nextChild = n[cindex];
          if (nextChild.getKind() == NOT)
          {
            nextChild = nextChild[0];
            invertChild = !invertChild;
          }
          // the relevance value of the child is based on the relevance value of
          // this, possibly inverted in nextChild was negated or is the first
          // child of IMPLIES.
          SatValue crval = invertChild ? invertValue(rval) : rval;
          markRelevant(nextChild, crval, toVisit);
        }
        currInfo->d_childIndex = cindex + 1;
      }
    }
  }
  else if (nk == ITE || (nk == EQUAL && n[0].getType().isBoolean())
           || nk == XOR)
  {
    Assert(cindex <= n.getNumChildren());
    if (cindex == 0)
    {
      // watch the first child with unknown polarity
      markRelevant(n[0], SAT_VALUE_UNKNOWN, toVisit);
      currInfo->d_childIndex = cindex + 1;
    }
    else
    {
      // check the value of last child
      SatValue cval = d_jcache.lookupValue(n[cindex - 1]);
      if (cval == SAT_VALUE_UNKNOWN)
      {
        // value is unknown, we are done for now
        // mark watch from n[cindex-1] to this
        markWatchedParent(n[cindex - 1], n);
        toVisit.pop_back();
        return SAT_VALUE_UNKNOWN;
      }
      else if (cindex == 1)
      {
        // set the child index to the index of relevant child + 1
        // visit the relevant child
        size_t rcindex;
        SatValue rcval;
        if (nk == ITE)
        {
          // take the relevant branch, whose relevance is equal to this
          rcindex = cval == SAT_VALUE_TRUE ? 2 : 3;
          rcval = rval;
        }
        else
        {
          // take the right hand side, whose relevance may be inverted based on
          // the value of the left hand side.
          rcindex = 2;
          bool invertChild =
              (cval == (nk == EQUAL ? SAT_VALUE_FALSE : SAT_VALUE_TRUE));
          rcval = invertChild ? invertValue(rval) : rval;
        }
        TNode nextChild = n[rcindex - 1];
        markRelevant(nextChild, rcval, toVisit);
        currInfo->d_childIndex = rcindex;
      }
      else
      {
        toVisit.pop_back();
        if (nk == ITE)
        {
          // the value of this is the value of the branch
          newJval = cval;
        }
        else
        {
          // look up the value of the first child and compute the result
          SatValue cval0 = d_jcache.lookupValue(n[0]);
          Assert(cval0 != SAT_VALUE_UNKNOWN);
          newJval = (nk == XOR ? cval != cval0 : cval == cval0)
                        ? SAT_VALUE_TRUE
                        : SAT_VALUE_FALSE;
        }
      }
    }
  }
  else if (cindex == 0)
  {
    Trace("prop-finder-debug")
        << "...preregister theory literal " << n << std::endl;
    // theory literals are added to the preregister queue
    toVisit.pop_back();
    toPreregister.push_back(n);
    d_statPrereg = d_statPrereg + 1;
    Trace("prop-finder-status") << "Preregistered " << d_statPrereg << " / "
                                << d_statSatPrereg << " literals" << std::endl;
    // this ensures we don't preregister the same literal twice
    currInfo->d_childIndex = 1;
    currInfo->d_rval = SAT_VALUE_UNKNOWN;
    // don't need to bother setting justified as the value of theory atoms is
    // handled in justify cache.
  }
  return newJval;
}

void PropFinder::markRelevant(TNode n,
                              SatValue val,
                              std::vector<TNode>& toVisit)
{
  // TODO: short cut if n is a theory literal, don't allocate cinfo?
  // problem is that adding to preregister has to be handled somewhere
  if (n.getKind() == NOT)
  {
    n = n[0];
    val = invertValue(val);
  }
  Assert(n.getKind() != NOT);
  // if we already have a value, don't bother
  if (d_jcache.hasValue(n))
  {
    return;
  }
  PropFindInfo* currInfo = getInfo(n);
  // if we haven't allocated yet, set the relevance value directly
  if (currInfo == nullptr)
  {
    Trace("prop-finder-debug")
        << "Mark " << n << " as relevant with polarity " << val << std::endl;
    currInfo = mkInfo(n);
    currInfo->d_rval = val;
    toVisit.emplace_back(n);
    return;
  }
  // Otherwise, take the union of relevant values. If we update our relevant
  // values, then we require processing relevance again.
  SatValue prevVal = currInfo->d_rval;
  SatValue newVal = relevantUnion(val, prevVal);
  if (newVal != prevVal)
  {
    Trace("prop-finder-debug")
        << "Mark (update) " << n << " as relevant with polarity " << newVal
        << std::endl;
    // update relevance value and reset counters
    currInfo->d_rval = newVal;
    currInfo->d_childIndex = 0;
    currInfo->d_iter = 0;
    toVisit.emplace_back(n);
  }
  // otherwise did not update, don't add to stack.
}

void PropFinder::markWatchedParent(TNode child, TNode parent, SatValue implJustify)
{
  Trace("prop-finder-debug")
      << "Mark watched " << child << " with parent " << parent << std::endl;
  bool ppol = (child.getKind() != NOT);
  TNode childAtom = ppol ? child : child[0];
  Assert(childAtom.getKind() != NOT);
  Assert(parent.getKind() != NOT);
  PropFindInfo* currInfo = getOrMkInfo(childAtom);
  // add to parent list
  currInfo->d_parentList.push_back(parent);
  // if we imply the justification of the parent (perhaps with a negation)
  if (implJustify!=SAT_VALUE_UNKNOWN)
  {
    currInfo->d_parentListPol[parent] = implJustify==SAT_VALUE_FALSE ? !ppol : ppol;
  }
}

void PropFinder::updateJustify(std::vector<std::pair<TNode, SatValue>>& justifyQueue, std::vector<TNode>& toVisit)
{
  size_t i = 0;
  std::pair<TNode, SatValue> curr;
  TNode n;
  SatValue val;
  while (i<justifyQueue.size())
  {
    curr = justifyQueue[i];
    n = curr.first;
    val = curr.second;
    i++;
    Assert(n.getKind() != NOT);
    PropFindInfo* currInfo = getInfo(n);
    if (currInfo != nullptr)
    {
      std::map<Node, bool>::iterator itj;
      std::map<Node, bool>& pl = currInfo->d_parentListPol;
      for (const Node& p : currInfo->d_parentList)
      {
        itj = pl.find(p);
        if (itj!=pl.end())
        {
          Kind pk = p.getKind();
          Assert (pk==AND || pk==OR || pk==IMPLIES);
          // propagate justification upwards
          bool childVal = (val == (itj->second ? SAT_VALUE_TRUE : SAT_VALUE_FALSE));
          // does it force the value?
          if ((pk==AND)!=childVal)
          {
            if (!d_jcache.hasValue(p))
            {
              prop::SatValue newPJval =  childVal ? SAT_VALUE_TRUE : SAT_VALUE_FALSE;
              Trace("prop-finder-debug") << "Due to setting " << n << " to " << val << ", parent " << p << " now has value " << newPJval << std::endl;
              d_jcache.setValue(p, newPJval);
              justifyQueue.emplace_back(p, newPJval);
            }
            continue;
          }
        }
        // otherwise, must update relvance on the parent
        toVisit.emplace_back(p);
      }
    }
  }
}

PropFindInfo* PropFinder::getInfo(TNode n)
{
  context::CDInsertHashMap<Node, std::shared_ptr<PropFindInfo>>::const_iterator
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

SatValue PropFinder::relevantUnion(SatValue r1, SatValue r2)
{
  return r1 == r2 ? r1 : SAT_VALUE_UNKNOWN;
}

}  // namespace decision
}  // namespace cvc5::internal
