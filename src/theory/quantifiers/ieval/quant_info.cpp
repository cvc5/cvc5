/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Info per quantified formula in CCFV.
 */

#include "theory/quantifiers/ieval/quant_info.h"

#include "expr/node_algorithm.h"
#include "expr/term_canonize.h"
#include "theory/quantifiers/ematching/trigger_term_info.h"
#include "theory/quantifiers/term_database.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

QuantInfo::QuantInfo(context::Context* c)
    : d_isActive(c, true), d_maybeConflict(c, true)
{
}

void QuantInfo::initialize(TNode q,
                           TermDb* tdb,
                           expr::TermCanonize& tc)
{
  Assert(q.getKind() == FORALL);
  d_quant = q;

  Trace("ieval-quant-debug")
      << "Register quant " << d_quant.getId() << " : " << d_quant << std::endl;

  // canonize the body of the quantified formula
  Trace("ieval-quant-debug") << "Get canonized body..." << std::endl;
  std::map<TNode, Node> visited;
  d_canonBody = tc.getCanonicalTerm(q[1], visited);

  // compute the variable correspondence
  Trace("ieval-quant-debug")
      << "Compute variable correspondence..." << std::endl;
  std::map<TNode, Node>::iterator it;
  std::vector<std::pair<size_t, TNode>> varList;
  std::vector<TNode> uncontainedVar;
  for (const Node& v : q[0])
  {
    it = visited.find(v);
    if (it != visited.end())
    {
      TNode cv = it->second;
      d_canonVars.push_back(cv);
      size_t index = tc.getIndexForFreeVariable(cv);
      varList.push_back(std::pair<size_t, TNode>(index, cv));
    }
    else
    {
      Assert(false);
      d_canonVars.push_back(v);
      uncontainedVar.push_back(v);
    }
  }
  // Sort variables by their index in the term canonizer. This is to ensure
  // a variable ordering in the driver where shared variables are assigned
  // first.
  Trace("ieval-quant-debug") << "Compute variable order..." << std::endl;
  std::sort(varList.begin(), varList.end());
  for (std::pair<size_t, TNode>& vl : varList)
  {
    d_canonVarOrdered.push_back(vl.second);
  }

  // compute matching requirements
  Trace("ieval-quant-debug") << "Compute constraints..." << std::endl;
  std::unordered_set<TNode> processed;
  std::unordered_set<TNode>::iterator itp;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(d_canonBody);
  do
  {
    cur = visit.back();
    visit.pop_back();
    itp = processed.find(cur);
    if (itp == processed.end())
    {
      processed.insert(cur);
      // process the match requirement for (disjunct) cur
      computeMatchReq(cur, ee, visit);
    }
  } while (!visit.empty());

  // now we go back and process terms in the match requirements
  Trace("ieval-quant-debug") << "Process terms..." << std::endl;
  processMatchReqTerms(tdb);

  // debug print
  Trace("ieval-quant") << toStringDebug();
}

std::string QuantInfo::toStringDebug() const
{
  std::stringstream ss;
  ss << "--- QuantInfo for " << d_quant.getId() << std::endl;
  ss << "Body: " << d_canonBody << std::endl;
  ss << "Vars: " << d_canonVarOrdered << std::endl;
  ss << "Constraints:" << std::endl;
  if (d_req.empty())
  {
    ss << "  (none)" << std::endl;
  }
  else
  {
    for (const std::pair<const TNode, std::vector<Node>>& r : d_req)
    {
      ss << "  " << r.first << " -> " << r.second << std::endl;
    }
  }
  ss << "Congruence terms: " << d_congTerms << std::endl;
  if (!d_varToFinalTerms.empty())
  {
    ss << "Variable to final terms:" << std::endl;
    for (const std::pair<const TNode, std::vector<TNode>>& t :
         d_varToFinalTerms)
    {
      ss << "  " << t.first << " -> " << t.second << std::endl;
    }
  }
  if (!d_candidateMatchers.empty())
  {
    ss << "Candidate matchers:" << std::endl;
    for (const std::pair<const TNode, std::vector<TNode>>& t :
         d_candidateMatchers)
    {
      ss << "  " << t.first << " -> " << t.second << std::endl;
    }
  }
  if (!d_matcherToCScore.empty())
  {
    ss << "Matcher information:" << std::endl;
    std::map<TNode, std::vector<TNode>>::const_iterator itf;
    for (const std::pair<const TNode, size_t>& t : d_matcherToCScore)
    {
      ss << "  " << t.first << " : c-score = " << t.second;
      itf = d_matcherToFun.find(t.first);
      Assert(itf != d_matcherToFun.end());
      if (!itf->second.empty())
      {
        ss << ", funs = " << itf->second;
      }
      ss << std::endl;
    }
  }
  if (!d_evalArgTerms.empty())
  {
    ss << "Evaluate argument terms: " << d_evalArgTerms << std::endl;
  }
  return ss.str();
}

void QuantInfo::computeMatchReq(TNode cur,
                                std::vector<TNode>& visit)
{
  Assert(cur.getType().isBoolean());
  bool pol = true;
  Kind k = cur.getKind();
  Assert(k != IMPLIES);
  if (k == OR)
  {
    // decompose OR
    visit.insert(visit.end(), cur.begin(), cur.end());
    return;
  }
  else if (k == NOT)
  {
    pol = false;
    cur = cur[0];
    k = cur.getKind();
    // double negations should already be eliminated
    Assert(k != NOT);
  }
  // NOTE: could sanitize the term, remove any nested quantifiers here?
  // This is probably not necessary, the equality engine will treat the term
  // as a leaf.

  // P(x) V (Q(x) ^ R(x)) V f(x) = a V R(f(x)) V f(x) != g(x)
  // P(x) -> false
  // (Q(x) ^ R(x)) -> false
  // f(x) -> (not (= f(x) a))
  // R(f(x)) -> false
  // f(x)=g(x) -> true
  if (k == EQUAL)
  {
    // maybe pattern equals ground?
    for (size_t i = 0; i < 2; i++)
    {
      if (!expr::hasBoundVar(cur[i]))
      {
        // Equality involving a ground term.
        // Flip polarity since we want to falsify.
        addMatchTermReq(cur[1 - i], cur[i], !pol);
        return;
      }
    }
  }
  if (k == EQUAL || tdb->isMatchable(cur) || expr::isBooleanConnective(cur))
  {
    // Equality between patterns, matchable predicate, or Boolean connective.
    // Note that equalities and Boolean connectives are simply marked as
    // constraints here, the main algorithm will determine how to process them.
    // Flip polarity since we want to falsify.
    Node eqc = NodeManager::currentNM()->mkConst(!pol);
    addMatchTermReq(cur, eqc, true);
    return;
  }
  // Unmatchable predicate, add all of its children without polarity.
  for (TNode lc : cur)
  {
    // to be propagating, it must be equal to something
    addMatchTermReq(lc, Node::null(), true);
  }
}

void QuantInfo::addMatchTermReq(TNode t, Node eqc, bool isEq)
{
  // notice that in rare cases, t may have no free variables, e.g.
  // if miniscoping is disabled, or there is a ground subterm in a non-entailed
  // position.

  // if not equal, make into disequality constraint (not (= t eqc))
  if (!isEq)
  {
    Assert(!eqc.isNull());
    eqc = t.eqNode(eqc).notNode();
  }
  std::vector<Node>& reqs = d_req[t];
  if (std::find(reqs.begin(), reqs.end(), eqc) == reqs.end())
  {
    reqs.push_back(eqc);
  }
}

void QuantInfo::processMatchReqTerms(TermDb* tdb)
{
  // Now, traverse each of the terms in match requirements. This sets up:
  // (1) d_congTerms, the set of terms we are doing congruence over
  // (2) d_matchers, the set of terms that we may do matching with,
  // which is the set of terms in the body of ee that do not occur beneath
  // a congruence term.
  // (3) d_evalArgTerms, the set of subterms we don't know how to handle.
  // (4) d_varToFinalTerms, which maps variables to the terms that are
  // final when they are assigned

  // We track pairs (t, b) where t is the term we are traversing, and b is
  // whether we have traversed inside a congruence term.
  std::unordered_map<std::pair<TNode, bool>, bool, NodeBoolPairHashFunction>
      visited;
  std::unordered_map<std::pair<TNode, bool>, bool, NodeBoolPairHashFunction>::
      iterator it;
  std::vector<std::pair<TNode, bool>> visit;
  std::pair<TNode, bool> cur;
  // set d_reqTerms and add them all for traversal
  for (const std::pair<const TNode, std::vector<Node>>& r : d_req)
  {
    d_reqTerms.push_back(r.first);
    visit.push_back(std::pair<TNode, bool>(r.first, false));
  }
  Trace("ieval-quant-debug") << "Traverse terms..." << std::endl;
  // track parents list
  std::map<TNode, std::vector<TNode>> parentList;
  std::unordered_set<TNode> topLevelMatchers;
  // traverse
  while (!visit.empty())
  {
    cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      if (!isTraverseTerm(cur.first))
      {
        // a term that should never be traversed, e.g. a nested closure
        visit.pop_back();
        visited[cur] = true;
        continue;
      }
      else if (!expr::hasBoundVar(cur.first))
      {
        // don't traverse terms without variables, although we do add these
        // as congruence terms.
        visited[cur] = false;
        continue;
      }
      Kind k = cur.first.getKind();
      bool inCongTerm = cur.second;
      // if we are a variable, or do congruence over this kind
      if (k == BOUND_VARIABLE || tdb->isMatchable(cur.first))
      {
        if (!inCongTerm)
        {
          // record top level matcher
          topLevelMatchers.insert(cur.first);
          // we are now within a congruence term
          visit.pop_back();
          visited[cur] = true;
          // Mark to visit self as non-top level. This ensures we only add each
          // term to d_congTerms once.
          visit.push_back(std::pair<TNode, bool>(cur.first, true));
          continue;
        }
        else
        {
          // will add to congruence terms at post-traversal
          visited[cur] = false;
        }
      }
      else if (!inCongTerm)
      {
        // if we are not a congruence term, and we are not in a congruence term,
        // recurse
        visit.pop_back();
        visited[cur] = true;
      }
      else
      {
        // we are in a congruence term, but we are not a congruence kind,
        // e.g. we are (+ x 1) in the term (P (+ x 1)). We traverse to
        // add x and 1, noting the children are not in a congruence term.
        // We furthermore add this to the list of evaluate arg terms.
        d_evalArgTerms.push_back(cur.first);
        visit.pop_back();
        visited[cur] = true;
        inCongTerm = false;
      }
      // recurse to children
      if (cur.first.getNumChildren() > 0)
      {
        for (TNode cc : cur.first)
        {
          visit.push_back(std::pair<TNode, bool>(cc, inCongTerm));
          // remember the parent list
          parentList[cc].push_back(cur.first);
        }
      }
    }
    else
    {
      visit.pop_back();
      if (!it->second)
      {
        visited[cur] = true;
        // we will add this term to the equality engine. We add at post-order
        // traversal to that the order of terms is correct, i.e. we add subterms
        // first.
        d_congTerms.push_back(cur.first);
      }
    }
  }
  Trace("ieval-quant-debug") << "Compute candidate matchers..." << std::endl;
  std::unordered_set<std::pair<TNode, bool>, NodeBoolPairHashFunction>::iterator
      itc;
  std::unordered_set<TNode>::iterator itm;
  std::map<TNode, std::vector<TNode>>::iterator itpl;
  std::map<TNode, TNode> termToMaxVar;
  std::vector<std::pair<TNode, bool>> ctnVisit;
  for (TNode v : d_canonVarOrdered)
  {
    // for each variable, visit the parents list, tracking whether we are in
    // a matchable context.
    std::unordered_set<std::pair<TNode, bool>, NodeBoolPairHashFunction>
        containing;
    ctnVisit.push_back(std::pair<TNode, bool>(v, true));
    do
    {
      cur = ctnVisit.back();
      ctnVisit.pop_back();
      itc = containing.find(cur);
      if (itc == containing.end())
      {
        containing.insert(cur);
        // if this is a matchable context, and we are a top-level matcher
        bool isMatchable =
            cur.second && (cur.first == v || tdb->isMatchable(cur.first));
        if (isMatchable)
        {
          itm = topLevelMatchers.find(cur.first);
          if (itm != topLevelMatchers.end())
          {
            d_candidateMatchers[v].push_back(cur.first);
            registerCandidateMatcher(tdb, cur.first);
          }
        }
        // we have fvars[i] < fvars[j] for i < j, set or overwrite the max
        // variable here. For example, for ordering x<y<z<w, d_termMaxVar maps:
        //   f(x,y) -> y, f(x,z) -> z, f(y) -> y
        // which will be converted in d_varToFinalTerms below to:
        //   y->[f(x,y), f(y)], z -> [f(x,z)]
        // which determines when terms are fully assigned.
        termToMaxVar[cur.first] = v;
        itpl = parentList.find(cur.first);
        if (itpl != parentList.end())
        {
          for (TNode p : itpl->second)
          {
            ctnVisit.push_back(std::pair<TNode, bool>(p, isMatchable));
          }
        }
      }
    } while (!ctnVisit.empty());
  }
  // set the final terms
  std::map<TNode, TNode>::iterator ittf;
  for (TNode ct : d_congTerms)
  {
    if (ct.getKind() == BOUND_VARIABLE)
    {
      // don't need to mark free variables as final
      continue;
    }
    ittf = termToMaxVar.find(ct);
    if (ittf != termToMaxVar.end())
    {
      d_varToFinalTerms[ittf->second].push_back(ct);
    }
    else
    {
      // otherwise marked as null, will be notified immediately at the beginning
      // of CCFV search
      d_varToFinalTerms[Node::null()].push_back(ct);
    }
  }
}

void QuantInfo::registerCandidateMatcher(TermDb* tdb, TNode m)
{
  if (d_matcherToCScore.find(m) != d_matcherToCScore.end())
  {
    // already registered
    return;
  }
  // compute the constraint score
  size_t cscore = 0;
  std::map<TNode, std::vector<Node>>::iterator itr = d_req.find(m);
  if (itr != d_req.end())
  {
    for (const Node& cs : itr->second)
    {
      if (cs.isNull())
      {
        cscore = 2;
      }
      else if (isDeqConstraint(cs, m))
      {
        cscore = 4;
      }
      else
      {
        cscore = 6;
        break;
      }
    }
  }
  // compute the functions that we have to match for this
  std::vector<TNode>& funs = d_matcherToFun[m];
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(m);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (!isTraverseTerm(cur) || !expr::hasBoundVar(cur))
      {
        // ignore no-traverse and ground terms
        continue;
      }
      // if the term is matchable, note its match operator
      Node matchOp = tdb->getMatchOperator(cur);
      if (!matchOp.isNull())
      {
        // note: should be a congruence kind???
        if (std::find(funs.begin(), funs.end(), matchOp) == funs.end())
        {
          funs.push_back(matchOp);
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());
  if (!funs.empty())
  {
    cscore = cscore + 1;
  }
  d_matcherToCScore[m] = cscore;
}

void QuantInfo::resetRound(TermDb* tdb)
{
  d_isActive = true;
  d_initVarIndex = 0;

  d_matchers.clear();
  std::unordered_set<TNode> usedMatchers;
  std::map<TNode, std::vector<TNode>>::iterator itcm;
  bool feasible = true;
  for (TNode v : d_canonVarOrdered)
  {
    TNode m = getBestMatcherFor(tdb, v, usedMatchers, feasible);
    // could have realized by setting up matching that we will never be
    // propagating
    if (!feasible)
    {
      d_isActive = false;
      return;
    }
    if (!m.isNull())
    {
      Trace("ieval-matching") << "Matcher (" << d_quant.getId() << ", " << v
                             << ") = " << m << std::endl;
      // use the matcher for this variable
      d_matchers[v] = m;
      Assert(expr::hasSubterm(m, v));
      // Notice that variables in d_canonVarOrdered are assigned in order,
      // thus this justifies matching for future variables.
      usedMatchers.insert(m);
    }
    else
    {
      // Warn that no matchers exist?
      Trace("ieval-warn") << "Warning: no matcher exists for variable " << v
                         << " in " << d_quant << std::endl;
    }
  }
}

TNode QuantInfo::getBestMatcherFor(TermDb* tdb,
                                   TNode v,
                                   std::unordered_set<TNode>& usedMatchers,
                                   bool& feasible)
{
  std::map<TNode, std::vector<TNode>>::iterator itcm =
      d_candidateMatchers.find(v);
  if (itcm == d_candidateMatchers.end())
  {
    return TNode::null();
  }
  TNode best;
  TNode alreadyMatcher;
  std::pair<size_t, int64_t> bestScore;
  std::map<TNode, size_t> matchMinScore;
  std::map<TNode, size_t>::iterator itmm;
  // for each candidate matcher
  for (TNode m : itcm->second)
  {
    // get their heuristic scores for constraints, matching
    size_t cscore = d_matcherToCScore[m];
    size_t mmscore = 0;
    itmm = matchMinScore.find(m);
    if (itmm == matchMinScore.end())
    {
      mmscore = getMinMatchCount(tdb, m);
      matchMinScore[m] = mmscore;
    }
    else
    {
      mmscore = itmm->second;
    }
    if (cscore >= 2 && mmscore == 0)
    {
      // we are done if there is a constraint term that is infeasible to match
      feasible = false;
      return TNode::null();
    }
    // if we already used it for a previous variable, use it for this one
    // as well?
    if (alreadyMatcher.isNull())
    {
      // if we already used it for a previous variable, use it for this one
      // as well?
      if (usedMatchers.find(m) != usedMatchers.end())
      {
        alreadyMatcher = m;
      }
      else
      {
        // prefer matchers in increasing order:
        // 0-no constraints, 1-null constraint, 2-disequality, 3-equality
        std::pair<size_t, int64_t> mscore =
            std::pair<size_t, int64_t>(cscore, -mmscore);
        if (best.isNull() || mscore > bestScore)
        {
          // Take this as the new best candidate matcher
          best = m;
          bestScore = mscore;
        }
      }
    }
  }
  return alreadyMatcher.isNull() ? best : alreadyMatcher;
}

size_t QuantInfo::getMinMatchCount(TermDb* tdb, TNode m) const
{
  std::map<TNode, std::vector<TNode>>::const_iterator it =
      d_matcherToFun.find(m);
  Assert(it != d_matcherToFun.end());
  size_t count = 0;
  bool hasSet = false;
  for (TNode f : it->second)
  {
    size_t numF = tdb->getNumGroundTerms(f);
    if (!hasSet || numF < count)
    {
      hasSet = true;
      count = numF;
      if (count == 0)
      {
        // term requires a matcher with zero arguments
        break;
      }
    }
  }
  return count;
}

TNode QuantInfo::getNextSearchVariable()
{
  if (d_initVarIndex >= d_canonVarOrdered.size())
  {
    return TNode::null();
  }
  TNode next = d_canonVarOrdered[d_initVarIndex];
  d_initVarIndex++;
  return next;
}

TNode QuantInfo::getMatcherFor(TNode v) const
{
  std::map<TNode, TNode>::const_iterator it = d_matchers.find(v);
  if (it == d_matchers.end())
  {
    return TNode::null();
  }
  return it->second;
}

const std::vector<TNode>& QuantInfo::getFreeVariables() const
{
  return d_canonVars;
}

const std::vector<TNode>& QuantInfo::getOrderedFreeVariables() const
{
  return d_canonVarOrdered;
}

const std::map<TNode, std::vector<Node>>& QuantInfo::getConstraints() const
{
  return d_req;
}

const std::vector<TNode>& QuantInfo::getConstraintTerms() const
{
  return d_reqTerms;
}
const std::vector<TNode>& QuantInfo::getCongruenceTerms() const
{
  return d_congTerms;
}

const std::vector<TNode>& QuantInfo::getEvalArgTerms() const
{
  return d_evalArgTerms;
}

const std::map<TNode, std::vector<TNode>>& QuantInfo::getVarToFinalTermMap()
    const
{
  return d_varToFinalTerms;
}

bool QuantInfo::isActive() const { return d_isActive.get(); }

void QuantInfo::setActive(bool val) { d_isActive = val; }

void QuantInfo::setNoConflict() { d_maybeConflict = false; }

bool QuantInfo::isMaybeConflict() const { return d_maybeConflict.get(); }

bool QuantInfo::isTraverseTerm(TNode n) { return !n.isClosure(); }

bool QuantInfo::isDeqConstraint(TNode c, TNode p)
{
  return c.getKind() == NOT && c[0].getKind() == EQUAL && c[0][0] == p;
}

bool QuantInfo::isDeqConstraint(TNode p, TNode c, TNode& val)
{
  if (isDeqConstraint(c, p))
  {
    val = c[0][1];
    return true;
  }
  return false;
}

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
