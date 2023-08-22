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
 * Relevant preregistration policy
 */

#include "prop/relevant_preregistrar.h"

#include "options/prop_options.h"
#include "expr/skolem_manager.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace prop {

RlvInfo::RlvInfo(context::Context* c)
    : d_iter(c, 0),
      d_rval(c, SAT_VALUE_UNKNOWN),
      d_childIndex(c, 0),
      d_parentList(c)
{
}

RelevantPreregistrar::RelevantPreregistrar(Env& env,
                                           CDCLTSatSolver* ss,
                                           CnfStream* cs)
    : EnvObj(env),
      d_pstate(context()),
      d_assertions(userContext()),
      d_preregistered(context()),
      d_assertionIndex(context(), 0),
      d_jcache(context(), ss, cs),
      d_statSatPrereg(context(), 0),
      d_statPrereg(context(), 0)

{
}

RelevantPreregistrar::~RelevantPreregistrar() {}

void RelevantPreregistrar::check(std::vector<TNode>& toPreregister)
{
  // ensure that all assertions have been marked as relevant
  size_t asize = d_assertions.size();
  while (d_assertionIndex.get() < asize)
  {
    TNode n = d_assertions[d_assertionIndex];
    setRelevant(n, toPreregister);
    d_assertionIndex = d_assertionIndex + 1;
  }
}

void RelevantPreregistrar::addAssertion(TNode n, TNode skolem, bool isLemma)
{
  if (!skolem.isNull())
  {
    // skolem definitions handled dynamically
    return;
  }
  // buffer it into the list of assertions
  Trace("prereg-rlv") << "RelevantPreregistrar: add assertion " << n
                      << std::endl;
  d_assertions.push_back(n);
}

void RelevantPreregistrar::notifySatLiteral(TNode n)
{
  Trace("prereg-rlv") << "RelevantPreregistrar: notify SAT literal " << n
                      << std::endl;
  // do nothing, only for stats
  d_statSatPrereg = d_statSatPrereg + 1;
}

void RelevantPreregistrar::notifyActiveSkolemDefs(
    std::vector<TNode>& defs, std::vector<TNode>& toPreregister)
{
  for (TNode d : defs)
  {
    Trace("prereg-rlv") << "RelevantPreregistrar: add skolem definition " << d
                        << std::endl;
    setRelevant(d, toPreregister);
  }
}

bool RelevantPreregistrar::notifyAsserted(TNode n,
                                          std::vector<TNode>& toPreregister)
{
  Trace("prereg-rlv") << "RelevantPreregistrar: notify asserted " << n
                      << std::endl;
  bool pol = n.getKind() != kind::NOT;
  TNode natom = pol ? n : n[0];
  // update relevant, which will ensure that natom is preregistered if not
  // already done so
  setRelevant(natom, toPreregister);
  prop::SatValue jval = pol ? SAT_VALUE_TRUE : SAT_VALUE_FALSE;
  // if we haven't already set the value, set it now
  if (!d_jcache.hasValue(natom))
  {
    d_jcache.setValue(natom, jval);
  }
  std::vector<std::pair<TNode, SatValue>> justifyQueue;
  justifyQueue.emplace_back(natom, jval);
  std::vector<TNode> toVisit;
  updateJustify(justifyQueue, toVisit);
  Trace("prereg-rlv-debug2")
      << "...will visit " << toVisit.size() << " parents" << std::endl;
  updateRelevant(toVisit, toPreregister);

  // we are notified about Boolean variables, but these should not be asserted
  // to the theory engine unless they are from purification
  return isAtomPreregister(natom);
}

void RelevantPreregistrar::setRelevant(TNode n,
                                       std::vector<TNode>& toPreregister)
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
  updateRelevant(toVisit, toPreregister);
}

void RelevantPreregistrar::updateRelevant(std::vector<TNode>& toVisit,
                                          std::vector<TNode>& toPreregister)
{
  // list of (formula, polarity) that we have inferred in this call
  std::vector<std::pair<TNode, SatValue>> justifyQueue;
  TNode t;
  while (!toVisit.empty())
  {
    t = toVisit.back();
    Assert(t.getKind() != NOT);
    // update relevant
    SatValue jval = updateRelevantNext(t, toPreregister, toVisit);
    // if we found it was justified
    if (jval != SAT_VALUE_UNKNOWN)
    {
      Trace("prereg-rlv-debug")
          << "Mark " << t << " as justified " << jval << std::endl;
      // set its value in the justification cache
      d_jcache.setValue(t, jval);
      // add it to the queue for notifications
      justifyQueue.emplace_back(t, jval);
    }
    // If we are done processing relevance, process the justify queue, which may
    // add new parents to toVisit
    if (toVisit.empty())
    {
      updateJustify(justifyQueue, toVisit);
      justifyQueue.clear();
    }
  }
}

bool shouldWatchAll(Kind nk, SatValue rval)
{
  // NOTE: this could be changed to return false when rval == SAT_VALUE_UNKNOWN,
  // which would lead to fewer preregistrations. However, experiments have
  // shown it is better to return true in this case.
  return rval == SAT_VALUE_UNKNOWN || ((nk == AND) == (rval == SAT_VALUE_TRUE));
}

// NOTE: this method is responsible for popping from toVisit when applicable
SatValue RelevantPreregistrar::updateRelevantNext(
    TNode n, std::vector<TNode>& toPreregister, std::vector<TNode>& toVisit)
{
  Trace("prereg-rlv-debug2") << "Update relevance on " << n << std::endl;
  Assert(n.getKind() != NOT);
  RlvInfo* currInfo = getInfo(n);
  // we should have already been marked relevant
  Assert(currInfo != nullptr);
  // if we've justified already, we are done
  if (d_jcache.hasValue(n))
  {
    Trace("prereg-rlv-debug2") << "...already justified" << std::endl;
    toVisit.pop_back();
    return SAT_VALUE_UNKNOWN;
  }
  Kind nk = n.getKind();
  // the current relevance value we are processing
  SatValue rval = currInfo->d_rval;
  // if the justified value of n is found in this call, this is set to its value
  SatValue newJval = SAT_VALUE_UNKNOWN;
  size_t cindex = currInfo->d_childIndex;
  Trace("prereg-rlv-debug2")
      << "...relevance " << rval << ", childIndex " << cindex << ", iteration "
      << currInfo->d_iter << std::endl;
  Assert(cindex <= n.getNumChildren());
  if (nk == AND || nk == OR || nk == IMPLIES)
  {
    // the value that would imply our value
    SatValue forceVal = (nk == AND) ? SAT_VALUE_FALSE : SAT_VALUE_TRUE;
    // whether the current child is (implicitly) negated
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
        // value and we are in iter=0.
        // If we found an unknown child and aren't watching all children, we are
        // done for now.
        if (iter == 1 || !shouldWatchAll(nk, rval))
        {
          // mark watch from prevChild to this
          markWatchedParent(
              prevChild, n, invertChild ? SAT_VALUE_FALSE : SAT_VALUE_TRUE);
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
      // if we are at the end of children
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
          // otherwise, if d_iter=0, we will do another pass to check for
          // justification
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
    Trace("prereg-rlv") << "...preregister theory literal " << n << std::endl;
    // theory literals are added to the preregister queue
    toVisit.pop_back();
    if (isAtomPreregister(n))
    {
      toPreregister.push_back(n);
    }
    d_statPrereg = d_statPrereg + 1;
    Trace("prereg-rlv-status") << "Preregistered " << d_statPrereg << " / "
                               << d_statSatPrereg << " literals" << std::endl;
    // this ensures we don't preregister the same literal twice
    currInfo->d_childIndex = 1;
    currInfo->d_rval = SAT_VALUE_UNKNOWN;
    // don't need to bother setting justified as the value of theory atoms is
    // handled in justify cache.
  }
  return newJval;
}

void RelevantPreregistrar::markRelevant(TNode n,
                                        SatValue val,
                                        std::vector<TNode>& toVisit)
{
  // NOTE: we could short cut if n is a theory literal, don't allocate cinfo?
  // however, adding to preregister has to be handled somewhere
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
  RlvInfo* currInfo = getInfo(n);
  // if we haven't allocated yet, set the relevance value directly
  if (currInfo == nullptr)
  {
    Trace("prereg-rlv-debug")
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
    Trace("prereg-rlv-debug")
        << "Mark (update) " << n << " as relevant with polarity " << newVal
        << std::endl;
    // update relevance value and reset counters
    currInfo->d_rval = newVal;
    currInfo->d_childIndex = 0;
    currInfo->d_iter = 0;
    toVisit.emplace_back(n);
  }
  // otherwise did not update, don't add to toVisit.
}

void RelevantPreregistrar::markWatchedParent(TNode child,
                                             TNode parent,
                                             SatValue implJustify)
{
  Trace("prereg-rlv-debug")
      << "Mark watched " << child << " with parent " << parent << std::endl;
  bool ppol = (child.getKind() != NOT);
  TNode childAtom = ppol ? child : child[0];
  Assert(childAtom.getKind() != NOT);
  Assert(parent.getKind() != NOT);
  RlvInfo* currInfo = getOrMkInfo(childAtom);
  // add to parent list
  currInfo->d_parentList.push_back(parent);
  // if we imply the justification of the parent (perhaps with a negation)
  if (implJustify != SAT_VALUE_UNKNOWN)
  {
    currInfo->d_parentListPol[parent] =
        implJustify == SAT_VALUE_FALSE ? !ppol : ppol;
  }
}

void RelevantPreregistrar::updateJustify(
    std::vector<std::pair<TNode, SatValue>>& justifyQueue,
    std::vector<TNode>& toVisit)
{
  size_t i = 0;
  std::pair<TNode, SatValue> curr;
  TNode n;
  SatValue val;
  while (i < justifyQueue.size())
  {
    curr = justifyQueue[i];
    n = curr.first;
    val = curr.second;
    i++;
    Assert(n.getKind() != NOT);
    RlvInfo* currInfo = getInfo(n);
    if (currInfo != nullptr)
    {
      std::map<Node, bool>::iterator itj;
      std::map<Node, bool>& pl = currInfo->d_parentListPol;
      for (const Node& p : currInfo->d_parentList)
      {
        itj = pl.find(p);
        if (itj != pl.end())
        {
          Kind pk = p.getKind();
          Assert(pk == AND || pk == OR || pk == IMPLIES);
          // propagate justification upwards
          bool childVal =
              (val == (itj->second ? SAT_VALUE_TRUE : SAT_VALUE_FALSE));
          // does it force the value?
          if ((pk == AND) != childVal)
          {
            if (!d_jcache.hasValue(p))
            {
              prop::SatValue newPJval =
                  childVal ? SAT_VALUE_TRUE : SAT_VALUE_FALSE;
              Trace("prereg-rlv-debug")
                  << "Due to setting " << n << " to " << val << ", parent " << p
                  << " now has value " << newPJval << std::endl;
              d_jcache.setValue(p, newPJval);
              justifyQueue.emplace_back(p, newPJval);
            }
            continue;
          }
        }
        // otherwise, must update relevance on the parent
        toVisit.emplace_back(p);
      }
    }
  }
}

RlvInfo* RelevantPreregistrar::getInfo(TNode n)
{
  context::CDInsertHashMap<Node, std::shared_ptr<RlvInfo>>::const_iterator it =
      d_pstate.find(n);
  if (it != d_pstate.end())
  {
    return it->second.get();
  }
  return nullptr;
}

RlvInfo* RelevantPreregistrar::mkInfo(TNode n)
{
  Assert(d_pstate.find(n) == d_pstate.end());
  std::shared_ptr<RlvInfo> pi = std::make_shared<RlvInfo>(context());
  d_pstate.insert(n, pi);
  return pi.get();
}

RlvInfo* RelevantPreregistrar::getOrMkInfo(TNode n)
{
  RlvInfo* pi = getInfo(n);
  if (pi != nullptr)
  {
    return pi;
  }
  return mkInfo(n);
}

SatValue RelevantPreregistrar::relevantUnion(SatValue r1, SatValue r2)
{
  return r1 == r2 ? r1 : SAT_VALUE_UNKNOWN;
}

bool RelevantPreregistrar::isAtomPreregister(TNode n)
{
  if (!n.isVar())
  {
    // non-variable theory atom
    return true;
  }
  // only preregister variables corresponding to Boolean purification
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  return (sm->getId(n) == SkolemFunId::PURIFY);
}

}  // namespace prop
}  // namespace cvc5::internal
