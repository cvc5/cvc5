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
 * An assigner
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
  options::ConflictProcessMode mode = options().theory.conflictProcessMode;
  Assert(mode != options::ConflictProcessMode::NONE);
}

TrustNode ConflictProcessor::processLemma(const TrustNode& lem)
{
  ++d_stats.d_initLemmas;
  Node lemma = lem.getProven();
  lemma = rewrite(lemma);
  Subs s;
  std::map<Node, Node> varToExp;
  std::vector<TNode> tgtLits;
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
    return TrustNode::null();
  }
  // check if the substitution implies one of the tgtLit, if not, we are done
  Node tgtLit;
  for (TNode tlit : tgtLits)
  {
    if (checkSubstitution(s, tlit, true))
    {
      tgtLit = tlit;
      break;
    }
  }
  // the form of the target literal as it will appear in the final lemma.
  Node tgtLitFinal;
  std::vector<Node> auxExplain;
  if (tgtLit.isNull())
  {
    // NOTE: could do unification here
    Subs selim;
    std::vector<TNode> tgtLitsCheck = tgtLits;
    tgtLits.clear();
    for (TNode tlit : tgtLitsCheck)
    {
      Node v, ss;
      if (tlit.getKind()==Kind::NOT && isAssignEq(tlit[0], v, ss, false) && !selim.contains(v))
      {
        Node sss = selim.apply(ss);
        auxExplain.push_back(tlit);
        selim.add(v, sss);
      }
      else
      {
        tgtLits.push_back(tlit);
      }
    }
    // check tgtLits again
    if (!selim.empty())
    {
      for (TNode tlit : tgtLits)
      {
        Node tlits = selim.apply(tlit);
        if (checkSubstitution(s, tlits, true))
        {
          Trace("confp") << "...found target using " << selim.size() << " auxiliary equalities" << std::endl;
          tgtLit = tlit;
          tgtLitFinal = tlits;
          break;
        }
      }
    }
    if (tgtLit.isNull())
    {
      Trace("confp-debug") << "No target for " << lemma << std::endl;
      return TrustNode::null();
    }
  }
  else
  {
    tgtLitFinal = tgtLit;
  }
  bool minimized = false;
  // we are minimized if there were multiple target literals and we found a
  // single one that sufficed
  if (tgtLits.size() > 1)
  {
    minimized = true;
    ++d_stats.d_minLemmas;
    Trace("confp") << "Target suffices " << tgtLit
                   << " for more than one disjunct: " << lemma << std::endl;
  }
  // minimize the substitution here
  if (s.d_vars.size() > 1)
  {
    std::unordered_set<Node> symbols;
    expr::getSymbols(tgtLit, symbols);
    std::vector<Node> toErase;
    for (const Node& v : s.d_vars)
    {
      if (symbols.find(v) == symbols.end())
      {
        toErase.push_back(v);
      }
    }
    if (!toErase.empty())
    {
      if (!minimized)
      {
        minimized = true;
        ++d_stats.d_minLemmas;
      }
      for (const Node& v : toErase)
      {
        Trace("confp") << "Substitution for " << v
                       << " not necessary in: " << lemma << std::endl;
        s.erase(v);
        varToExp.erase(v);
      }
      Assert(!s.empty());
      // should still imply target
      Assert(checkSubstitution(s, tgtLit, true));
    }
  }

  // generalize the conflict
  bool isConflict = lem.getKind() == TrustNodeKind::CONFLICT;
  Trace("confp") << "...minimized=" << minimized << std::endl;
  // if we successfully generalized
  if (minimized)
  {
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
    if (tgtLitFinal.getKind() == Kind::OR)
    {
      clause.insert(clause.end(), tgtLitFinal.begin(), tgtLitFinal.end());
    }
    else
    {
      clause.push_back(tgtLitFinal);
    }
    Node genLem = nm->mkOr(clause);
    Trace("confp") << "...processed lemma is " << genLem << std::endl;
    // AlwaysAssert(false) << genLem << " for " << lem << std::endl;
    return TrustNode::mkTrustLemma(genLem);
  }
  return TrustNode::null();
}

void ConflictProcessor::decomposeLemma(const Node& lem,
                                       Subs& s,
                                       std::map<Node, Node>& varToExp,
                                       std::vector<TNode>& tgtLits) const
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
          if (isAssignEq(cur[0], vtmp, ctmp))
          {
            Node cprev = s.getSubs(vtmp);
            if (!cprev.isNull())
            {
              if (ctmp == cprev)
              {
                // redundant (duplicate equality)
                continue;
              }
              // just take this as a target literal
              tgtLits.push_back(cur);
              continue;
            }
            // use as a substitution
            s.add(vtmp, ctmp);
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

Node ConflictProcessor::evaluateSubstitution(const Subs& s,
                                             const Node& tgtLit) const
{
  return evaluate(tgtLit, s.d_vars, s.d_subs);
}

bool ConflictProcessor::checkSubstitution(const Subs& s,
                                          const Node& tgtLit,
                                          bool expect) const
{
  Node tgtAtom = tgtLit;
  if (tgtAtom.getKind() == Kind::NOT)
  {
    tgtAtom = tgtAtom[0];
    expect = !expect;
  }
  // optimize for OR, since we may have generalized a target
  Kind k = tgtAtom.getKind();
  if (k == Kind::OR || k == Kind::AND)
  {
    bool hasNonConst = false;
    for (const Node& n : tgtAtom)
    {
      Node sn = evaluateSubstitution(s, n);
      if (!sn.isConst())
      {
        // failure if all children must be a given value
        if (expect == (k == Kind::AND))
        {
          return false;
        }
        hasNonConst = true;
      }
      else if (sn.getConst<bool>() == (k == Kind::OR))
      {
        // success if short circuits to desired value
        return expect == (k == Kind::OR);
      }
    }
    return !hasNonConst;
  }
  // otherwise, rewrite
  Node stgtAtom = evaluateSubstitution(s, tgtAtom);
  return stgtAtom.isConst() && stgtAtom.getConst<bool>() == expect;
}

ConflictProcessor::Statistics::Statistics(StatisticsRegistry& sr)
    : d_initLemmas(sr.registerInt("ConflictProcessor::init_lemmas")),
      d_lemmas(sr.registerInt("ConflictProcessor::lemmas")),
      d_minLemmas(sr.registerInt("ConflictProcessor::min_lemmas"))
{
}

void ConflictProcessor::getEntailedEq(const Node& tc,
                                      const std::map<Node, size_t>& vindex,
                                      std::vector<Node>& entval)
{
  std::vector<Node> toCheck;
  Kind k = tc.getKind();
  if (k == Kind::AND)
  {
    toCheck.insert(toCheck.end(), tc.begin(), tc.end());
  }
  else if (k == Kind::EQUAL)
  {
    toCheck.push_back(tc);
  }
  Node vtmp;
  Node ctmp;
  std::map<Node, size_t>::const_iterator it;
  for (const Node& eq : toCheck)
  {
    if (!isAssignEq(eq, vtmp, ctmp))
    {
      continue;
    }
    it = vindex.find(vtmp);
    if (it == vindex.end())
    {
      continue;
    }
    Assert(it->second < entval.size());
    entval[it->second] = ctmp;
  }
}

bool ConflictProcessor::isAssignmentClashVec(const Node& a,
                                             const std::vector<Node>& entval)
{
  if (entval.size() == 1)
  {
    return isAssignmentClash(a, entval[0]);
  }
  Assert(a.getKind() == Kind::SEXPR && a.getNumChildren() == entval.size());
  for (size_t i = 0, nval = entval.size(); i < nval; i++)
  {
    if (isAssignmentClash(a[i], entval[i]))
    {
      return true;
    }
  }
  return false;
}
bool ConflictProcessor::isAssignmentClash(const Node& a, const Node& b)
{
  Assert(!a.isNull());
  return !b.isNull() && a.isConst() && b.isConst() && a != b;
}


bool ConflictProcessor::isAssignEq(const Node& n, Node& v, Node& c, bool reqConst)
{
  Kind k = n.getKind();
  if (k == Kind::EQUAL)
  {
    for (size_t i = 0; i < 2; i++)
    {
      if (n[i].isVar() && (!reqConst || n[1 - i].isConst()))
      {
        v = n[i];
        c = n[1 - i];
        return true;
      }
    }
  }
  return false;
}


}  // namespace theory
}  // namespace cvc5::internal
