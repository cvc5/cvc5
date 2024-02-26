/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Conflict processor module
 */

#include "theory/conflict_processor.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "theory/strings/regexp_eval.h"
#include "theory/theory_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

ConflictProcessor::ConflictProcessor(Env& env, TheoryEngine* te)
    : EnvObj(env), d_engine(te), d_stats(statisticsRegistry())
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
  options::ConflictProcessMode mode = options().theory.conflictProcessMode;
  d_useExtRewriter = (mode == options::ConflictProcessMode::MINIMIZE_EXT);
  Assert(mode != options::ConflictProcessMode::NONE);
}

TrustNode ConflictProcessor::processLemma(const TrustNode& lem)
{
  ++d_stats.d_initLemmas;
  Node lemma = lem.getProven();
  lemma = rewrite(lemma);
  // do not use compression
  SubstitutionMap s(nullptr, false);
  std::map<Node, Node> varToExp;
  std::vector<Node> tgtLits;
  // decompose lemma into AND( s ) => OR( tgtLits )
  decomposeLemma(lemma, s, varToExp, tgtLits);
  // if we didn't infer a substitution, we are done
  if (s.empty())
  {
    Trace("confp-nprocess") << "...no substitution for " << lemma << std::endl;
    return TrustNode::null();
  }
  ++d_stats.d_lemmas;
  Trace("confp") << "Decomposed " << lemma << std::endl;
  Trace("confp") << "- Substitution: " << s.toString() << std::endl;
  Trace("confp") << "- Target: " << tgtLits << std::endl;
  if (options().theory.conflictProcessMode
      == options::ConflictProcessMode::TEST)
  {
    Trace("confp") << "...FAIL (test)" << std::endl;
    return TrustNode::null();
  }
  // check if the substitution implies one of the tgtLit, if not, we are done
  Node tgtLit;
  std::vector<Node> tgtLitsNc;
  std::map<Node, Node> evMap;
  std::map<Node, Node>::iterator itm;
  for (const Node& tlit : tgtLits)
  {
    Node ev = evaluateSubstitution(s, tlit);
    Trace("confp-debug") << "eval " << tlit << " is " << ev << std::endl;
    if (ev == d_true)
    {
      tgtLit = tlit;
      break;
    }
    else if (ev == d_false)
    {
      Trace("confp-debug") << "...filter implied " << tlit << std::endl;
      continue;
    }
    if (!ev.isNull())
    {
      itm = evMap.find(ev);
      if (itm != evMap.end())
      {
        Trace("confp-debug") << "...filter duplicate " << tlit << std::endl;
        continue;
      }
      // look for negation??
      Node evn = ev.negate();
      itm = evMap.find(evn);
      if (itm != evMap.end())
      {
        tgtLitsNc.clear();
        Trace("confp-debug") << "...contradiction " << itm->second << " and "
                             << tlit << std::endl;
        tgtLitsNc.push_back(itm->second);
        tgtLitsNc.push_back(tlit);
        break;
      }
    }
    tgtLitsNc.push_back(tlit);
    evMap[ev] = tlit;
  }
  bool minimized = false;
  std::vector<Node> auxExplain;
  if (tgtLit.isNull())
  {
    Trace("confp-debug") << "No target for " << lemma << std::endl;
    // remove redundant
    if (tgtLitsNc.size() < tgtLits.size())
    {
      minimized = true;
      Trace("confp") << "...SUCCESS (filtered "
                     << (tgtLits.size() - tgtLitsNc.size()) << "/"
                     << tgtLits.size() << ")" << std::endl;
    }
    else
    {
      Trace("confp") << "...FAIL (no target)" << std::endl;
      return TrustNode::null();
    }
    // just take the OR as target
    tgtLit = NodeManager::currentNM()->mkOr(tgtLitsNc);
    // now try more aggressive substitutions?
  }
  else
  {
    if (tgtLits.size() > 1)
    {
      // we are minimized if there were multiple target literals and we found a
      // single one that sufficed
      minimized = true;
      Trace("confp") << "...SUCCESS (target out of " << tgtLits.size() << ")"
                     << std::endl;
      Trace("confp") << "Target suffices " << tgtLit
                     << " for more than one disjunct" << std::endl;
    }
    // NOTE: this substitution only applies when we found a literal, so it is
    // not done above minimize the substitution here
    std::unordered_map<Node, Node> smap = s.getSubstitutions();
    if (smap.size() > 1)
    {
      std::vector<Node> toErase;
      for (std::pair<const Node, Node>& ss : smap)
      {
        // try eliminating the substitution
        Node v = ss.first;
        s.eraseSubstitution(v);
        Trace("confp") << "--- try substitution without " << v << std::endl;
        if (checkSubstitution(s, tgtLit))
        {
          toErase.push_back(v);
        }
        else
        {
          Trace("confp") << "...did not work on " << tgtLit << std::endl;
          // add it back
          s.addSubstitution(v, ss.second);
        }
      }
      if (!toErase.empty())
      {
        if (TraceIsOn("confp"))
        {
          if (!minimized)
          {
            Trace("confp") << "...SUCCESS (min subs " << toErase.size() << "/"
                           << smap.size() << ")" << std::endl;
          }
        }
        minimized = true;
        for (const Node& v : toErase)
        {
          varToExp.erase(v);
          Trace("confp") << "Substitution is unnecessary for " << v
                         << std::endl;
        }
      }
    }
  }

  // bool isConflict = lem.getKind() == TrustNodeKind::CONFLICT;
  if (minimized)
  {
    ++d_stats.d_minLemmas;
    NodeManager* nm = NodeManager::currentNM();
    std::vector<Node> clause;
    for (std::pair<const Node, Node>& e : varToExp)
    {
      if (e.second.getKind() == Kind::AND)
      {
        for (const Node& ec : e.second)
        {
          clause.push_back(ec.negate());
        }
      }
      else
      {
        clause.push_back(e.second.negate());
      }
    }
    clause.insert(clause.end(), auxExplain.begin(), auxExplain.end());
    if (tgtLit.getKind() == Kind::OR)
    {
      clause.insert(clause.end(), tgtLit.begin(), tgtLit.end());
    }
    else
    {
      clause.push_back(tgtLit);
    }
    Node genLem = nm->mkOr(clause);
    Trace("confp") << "...processed lemma is " << genLem << std::endl;
    // AlwaysAssert(false) << genLem << " for " << lem << std::endl;
    return TrustNode::mkTrustLemma(genLem);
  }

  Trace("confp") << "...FAIL (no minimize)" << std::endl;
  return TrustNode::null();
}

void ConflictProcessor::decomposeLemma(const Node& lem,
                                       SubstitutionMap& s,
                                       std::map<Node, Node>& varToExp,
                                       std::vector<Node>& tgtLits) const
{
  // visit is implicitly negated
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  std::unordered_set<Node> keep;
  TNode cur;
  Kind k;
  visit.push_back(lem);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      k = cur.getKind();
      if (k == Kind::OR || k == Kind::IMPLIES)
      {
        // all children are entailed
        for (size_t i = 0, nargs = cur.getNumChildren(); i < nargs; i++)
        {
          if (k == Kind::IMPLIES && i == 0)
          {
            Node cc = cur[0].negate();
            keep.insert(cc);
            visit.push_back(cc);
          }
          else
          {
            visit.push_back(cur[i]);
          }
        }
        continue;
      }
      else if (k == Kind::NOT)
      {
        k = cur[0].getKind();
        if (k == Kind::EQUAL)
        {
          // maybe substitution?
          Node vtmp;
          Node ctmp;
          if (isAssignEq(s, cur[0], vtmp, ctmp))
          {
            Assert(!s.hasSubstitution(vtmp));
            // use as a substitution
            s.addSubstitution(vtmp, ctmp);
            varToExp[vtmp] = cur[0];
            continue;
          }
        }
        else if (k == Kind::AND)
        {
          // negations of children of AND are entailed
          for (const Node& c : cur[0])
          {
            Node cn = c.negate();
            keep.insert(cn);
            visit.push_back(cn);
          }
          continue;
        }
      }
      // otherwise, take this as a target literal
      tgtLits.push_back(cur);
    }
  } while (!visit.empty());
}

Node ConflictProcessor::evaluateSubstitutionLit(const SubstitutionMap& s,
                                                const Node& tgtLit) const
{
  Trace("confp-subs-debug") << "...try " << tgtLit << std::endl;
  Node ev = s.apply(tgtLit);
  Trace("confp-subs-debug") << "...apply " << ev << std::endl;
  // use the extended rewriter if option is set
  if (d_useExtRewriter)
  {
    ev = extendedRewrite(ev);
  }
  else
  {
    ev = rewrite(ev);
    // also try the extended equality rewriter
    if (ev.getKind() == Kind::EQUAL)
    {
      ev = rewriteEqualityExt(ev);
    }
  }
  Trace("confp-subs-debug") << "...rewrite " << ev << std::endl;
  return ev;
}

Node ConflictProcessor::evaluateSubstitution(const SubstitutionMap& s,
                                             const Node& tgtLit) const
{
  bool polarity = true;
  Node tgtAtom = tgtLit;
  if (tgtAtom.getKind() == Kind::NOT)
  {
    tgtAtom = tgtAtom[0];
    polarity = !polarity;
  }
  // optimize for OR, since we may have generalized a target
  Kind k = tgtAtom.getKind();
  if (k == Kind::OR || k == Kind::AND)
  {
    bool hasNonConst = false;
    for (const Node& n : tgtAtom)
    {
      Node sn = evaluateSubstitutionLit(s, n);
      if (!sn.isConst())
      {
        // failure if all children must be a given value
        if (polarity == (k == Kind::AND))
        {
          // we don't bother computing the rest
          return Node::null();
        }
        hasNonConst = true;
      }
      else if (sn.getConst<bool>() == (k == Kind::OR))
      {
        // short circuits to value
        return polarity ? sn : (k == Kind::OR ? d_false : d_true);
      }
    }
    // if non-constant, we don't bother computing
    return hasNonConst ? Node::null() : (k == Kind::OR ? d_true : d_false);
  }
  // otherwise, rewrite
  Node ret = evaluateSubstitutionLit(s, tgtAtom);
  if (!polarity)
  {
    return ret.isConst() ? (ret.getConst<bool>() ? d_false : d_true)
                         : ret.negate();
  }
  return ret;
}

bool ConflictProcessor::checkSubstitution(const SubstitutionMap& s,
                                          const Node& tgtLit) const
{
  Node ev = evaluateSubstitution(s, tgtLit);
  return ev == d_true;
}

ConflictProcessor::Statistics::Statistics(StatisticsRegistry& sr)
    : d_initLemmas(sr.registerInt("ConflictProcessor::init_lemmas")),
      d_lemmas(sr.registerInt("ConflictProcessor::lemmas")),
      d_minLemmas(sr.registerInt("ConflictProcessor::min_lemmas"))
{
}

bool ConflictProcessor::isAssignEq(const SubstitutionMap& s,
                                   const Node& n,
                                   Node& v,
                                   Node& c) const
{
  Assert(n.getKind() == Kind::EQUAL);
  for (size_t i = 0; i < 2; i++)
  {
    if (!n[i].isVar() || s.hasSubstitution(n[i]))
    {
      continue;
    }
    // otherwise check cyclic
    Node ns = s.apply(n[1 - i]);
    if (expr::hasSubterm(ns, n[i]))
    {
      continue;
    }
    v = n[i];
    c = n[1 - i];
    return true;
  }
  return false;
}

}  // namespace theory
}  // namespace cvc5::internal
