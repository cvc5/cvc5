/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of relevance manager.
 */

#include "theory/relevance_manager.h"

#include <sstream>

#include "expr/node_algorithm.h"
#include "expr/term_context_stack.h"
#include "options/smt_options.h"
#include "smt/env.h"
#include "theory/relevance_manager.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

RelevanceManager::RelevanceManager(Env& env, TheoryEngine* engine)
    : TheoryEngineModule(env, engine, "RelevanceManager"),
      d_val(engine),
      d_input(userContext()),
      d_atomMap(userContext()),
      d_rset(context()),
      d_inFullEffortCheck(false),
      d_fullEffortCheckFail(false),
      d_success(false),
      d_trackRSetExp(false),
      d_miniscopeTopLevel(true),
      d_rsetExp(context()),
      d_jcache(context())
{
  if (options().smt.produceDifficulty)
  {
    d_dman = std::make_unique<DifficultyManager>(env, this, d_val);
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
      // add to atoms map
      addInputToAtomsMap(a);
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
      // add to atoms map
      addInputToAtomsMap(a);
    }
    i++;
  }
}

void RelevanceManager::addInputToAtomsMap(TNode input)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(input);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (expr::isBooleanConnective(cur))
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
        continue;
      }
      NodeList* ilist = getInputListFor(cur);
      ilist->push_back(input);
    }
  } while (!visit.empty());
}

void RelevanceManager::check(Theory::Effort effort)
{
  if (Theory::fullEffort(effort))
  {
    d_inFullEffortCheck = true;
    d_fullEffortCheckFail = false;
  }
}

void RelevanceManager::postCheck(Theory::Effort effort)
{
  d_inFullEffortCheck = false;
}

void RelevanceManager::computeRelevance()
{
  // if not at full effort, should be tracking something else, e.g. explanation
  // for why literals are relevant.
  Assert(d_inFullEffortCheck || d_trackRSetExp);
  Trace("rel-manager") << "RelevanceManager::computeRelevance, full effort = "
                       << d_inFullEffortCheck << "..." << std::endl;
  // if we already failed
  if (d_fullEffortCheckFail)
  {
    d_success = false;
    return;
  }
  for (const Node& node: d_input)
  {
    if (!computeRelevanceFor(node))
    {
      d_success = false;
      return;
    }
  }
  if (TraceIsOn("rel-manager"))
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
  d_success = !d_fullEffortCheckFail;
}

bool RelevanceManager::computeRelevanceFor(TNode input)
{
  int32_t val = justify(input);
  if (val == -1)
  {
    // if we are in full effort check and fail to justify, then we should
    // give a failure and set success to false, or otherwise calls to
    // isRelevant cannot be trusted. It might also be the case that the
    // assertion has no value (val == 0), since it may correspond to an
    // irrelevant Skolem definition, in this case we don't throw a warning.
    if (d_inFullEffortCheck)
    {
      std::stringstream serr;
      serr << "RelevanceManager::computeRelevance: WARNING: failed to justify "
           << input;
      Trace("rel-manager") << serr.str() << std::endl;
      Assert(false) << serr.str();
      d_fullEffortCheckFail = true;
      return false;
    }
  }
  return true;
}

bool RelevanceManager::updateJustifyLastChild(const RlvPair& cur,
                                              std::vector<int32_t>& childrenJustify)
{
  // This method is run when we are informed that child index of cur
  // has justify status lastChildJustify. We return true if we would like to
  // compute the next child, in this case we push the status of the current
  // child to childrenJustify.
  size_t nchildren = cur.first.getNumChildren();
  Assert(expr::isBooleanConnective(cur.first));
  size_t index = childrenJustify.size();
  Assert(index < nchildren);
  Kind k = cur.first.getKind();
  // Lookup the last child's value in the overall cache, we may choose to
  // add this to childrenJustify if we return true.
  RlvPair cp(cur.first[index],
             d_ptctx.computeValue(cur.first, cur.second, index));
  Assert(d_jcache.find(cp) != d_jcache.end());
  int32_t lastChildJustify = d_jcache[cp];
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
    // add current child to list first before (possibly) computing result
    childrenJustify.push_back(lastChildJustify);
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

int32_t RelevanceManager::justify(TNode n)
{
  // The set of nodes that we have computed currently have no value. Those
  // that are marked as having no value in d_jcache must be recomputed, since
  // the values for SAT literals may have changed.
  std::unordered_set<RlvPair, RlvPairHashFunction> noJustify;
  // the vector of values of children
  std::unordered_map<RlvPair, std::vector<int32_t>, RlvPairHashFunction>
      childJustify;
  RlvPairIntMap::iterator it;
  std::unordered_map<RlvPair, std::vector<int32_t>, RlvPairHashFunction>::iterator
      itc;
  RlvPair cur;
  TCtxStack visit(&d_ptctx);
  visit.pushInitial(n);
  do
  {
    cur = visit.getCurrent();
    // should always have Boolean type
    Assert(cur.first.getType().isBoolean());
    it = d_jcache.find(cur);
    if (it != d_jcache.end())
    {
      if (it->second != 0 || noJustify.find(cur) != noJustify.end())
      {
        visit.pop();
        // already computed value
        continue;
      }
    }
    itc = childJustify.find(cur);
    // have we traversed to children yet?
    if (itc == childJustify.end())
    {
      // are we not a Boolean connective (including NOT)?
      if (expr::isBooleanConnective(cur.first))
      {
        // initialize its children justify vector as empty
        childJustify[cur].clear();
        // start with the first child
        visit.pushChild(cur.first, cur.second, 0);
      }
      else
      {
        visit.pop();
        // The atom case, lookup the value in the valuation class to
        // see its current value in the SAT solver, if it has one.
        int ret = 0;
        // otherwise we look up the value
        bool value;
        if (d_val.hasSatValue(cur.first, value))
        {
          ret = value ? 1 : -1;
          bool hasPol, pol;
          PolarityTermContext::getFlags(cur.second, hasPol, pol);
          // relevant if weakly matches polarity
          if (!hasPol || pol == value)
          {
            d_rset.insert(cur.first);
            if (d_trackRSetExp)
            {
              d_rsetExp[cur.first] = n;
              Trace("rel-manager-exp")
                  << "Reason for " << cur.first << " is " << n
                  << ", polarity is " << hasPol << "/" << pol << std::endl;
            }
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
        Assert(itc->second.size() < cur.first.getNumChildren());
        visit.pushChild(cur.first, cur.second, itc->second.size());
      }
      else
      {
        visit.pop();
        Assert(d_jcache.find(cur) != d_jcache.end());
        if (d_jcache[cur] == 0)
        {
          noJustify.insert(cur);
        }
      }
    }
  } while (!visit.empty());
  RlvPair ci(n, d_ptctx.initialValue());
  Assert(d_jcache.find(ci) != d_jcache.end());
  return d_jcache[ci];
}

bool RelevanceManager::isRelevant(TNode lit)
{
  Assert(d_inFullEffortCheck);
  // since this is used in full effort, and typically for all asserted literals,
  // we just ensure relevance is fully computed here
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

TNode RelevanceManager::getExplanationForRelevant(TNode lit)
{
  // agnostic to negation
  while (lit.getKind() == NOT)
  {
    lit = lit[0];
  }
  NodeList* ilist = nullptr;
  TNode nextInput;
  size_t ninputs = 0;
  size_t index = 0;
  do
  {
    // check if it has an explanation yet
    TNode exp = getExplanationForRelevantInternal(lit);
    if (!exp.isNull())
    {
      return exp;
    }
    // if the first time, we get the list of input formulas the atom occurs in
    if (index == 0)
    {
      ilist = getInputListFor(lit, false);
      if (ilist != nullptr)
      {
        ninputs = ilist->size();
      }
      Trace("rel-manager-exp-debug")
          << "Atom " << lit << " occurs in " << ninputs << " assertions..."
          << std::endl;
    }
    if (index < ninputs)
    {
      // justify the next
      nextInput = (*ilist)[index];
      index++;
      // justify the next input that the atom occurs in
      computeRelevanceFor(nextInput);
    }
    else
    {
      nextInput = TNode::null();
    }
  } while (!nextInput.isNull());

  return TNode::null();
}

TNode RelevanceManager::getExplanationForRelevantInternal(TNode atom) const
{
  NodeMap::const_iterator it = d_rsetExp.find(atom);
  if (it != d_rsetExp.end())
  {
    return it->second;
  }
  return TNode::null();
}

RelevanceManager::NodeList* RelevanceManager::getInputListFor(TNode atom,
                                                              bool doMake)
{
  NodeListMap::const_iterator it = d_atomMap.find(atom);
  if (it == d_atomMap.end())
  {
    if (!doMake)
    {
      return nullptr;
    }
    d_atomMap[atom] = std::make_shared<NodeList>(userContext());
    it = d_atomMap.find(atom);
  }
  return it->second.get();
}

std::unordered_set<TNode> RelevanceManager::getRelevantAssertions(bool& success)
{
  // set in full effort check temporarily
  d_inFullEffortCheck = true;
  d_fullEffortCheckFail = false;
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
  // reset in full effort check
  d_inFullEffortCheck = false;
  return rset;
}

void RelevanceManager::notifyLemma(TNode n,
                                   theory::LemmaProperty p,
                                   const std::vector<Node>& skAsserts,
                                   const std::vector<Node>& sks)
{
  // add to assertions
  if (options().theory.relevanceFilter && isLemmaPropertyNeedsJustify(p))
  {
    notifyPreprocessedAssertion(n, false);
    notifyPreprocessedAssertions(skAsserts, false);
  }
  // notice that we may be in FULL or STANDARD effort here.
  if (d_dman != nullptr)
  {
    // notice that we don't compute relevance here, instead it is computed
    // on demand based on the literals in n.
    d_dman->notifyLemma(n, d_inFullEffortCheck);
  }
}

bool RelevanceManager::needsCandidateModel()
{
  if (d_dman != nullptr)
  {
    return d_dman->needsCandidateModel();
  }
  return false;
}
void RelevanceManager::notifyCandidateModel(TheoryModel* m)
{
  if (d_dman != nullptr)
  {
    d_dman->notifyCandidateModel(m);
  }
}

void RelevanceManager::getDifficultyMap(std::map<Node, Node>& dmap,
                                        bool includeLemmas)
{
  if (d_dman != nullptr)
  {
    d_dman->getDifficultyMap(dmap, includeLemmas);
  }
}

}  // namespace theory
}  // namespace cvc5::internal
