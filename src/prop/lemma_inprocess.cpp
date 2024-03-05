/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Learner for literals asserted at level zero.
 */

#include "prop/lemma_inprocess.h"

#include "expr/node_algorithm.h"
#include "options/theory_options.h"
#include "prop/zero_level_learner.h"
#include "smt/env.h"

namespace cvc5::internal {
namespace prop {

LemmaInprocess::LemmaInprocess(Env& env, CnfStream* cs, ZeroLevelLearner& zll)
    : EnvObj(env),
      d_cs(cs),
      d_tsmap(zll.getSimplifications()),
      d_subsLitMap(userContext()),
      d_eqLitLemmas(userContext())
{
}
TrustNode LemmaInprocess::inprocessLemma(TrustNode& trn)
{
  if (trn.getKind() == TrustNodeKind::CONFLICT)
  {
    return trn;
  }
  const Node& proven = trn.getProven();
  Node provenp = processInternal(proven);
  if (provenp != proven)
  {
    Trace("lemma-inprocess-lemma")
        << "Inprocess " << proven << " returns " << provenp << std::endl;
    // proofs not supported
    return TrustNode::mkTrustNode(trn.getKind(), provenp);
  }
  return trn;
}

Node LemmaInprocess::processInternal(const Node& lem)
{
  std::vector<Node> eqLitLemmas;
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  context::CDHashMap<Node, Node>::iterator its;
  TNode cur;
  visit.emplace_back(lem);
  do
  {
    cur = visit.back();
    Trace("lemma-inprocess-visit") << "visit " << cur << std::endl;
    Assert(cur.getType().isBoolean());
    it = visited.find(cur);
    if (it == visited.end())
    {
      if (expr::isBooleanConnective(cur))
      {
        visited[cur] = Node::null();
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      else
      {
        visit.pop_back();
        // literal case
        bool prevLit = d_cs->hasLiteral(cur);
        Node scur = d_tsmap.get().apply(cur, d_env.getRewriter());
        its = d_subsLitMap.find(scur);
        if (its != d_subsLitMap.end())
        {
          if (cur != its->second)
          {
            Trace("lemma-inprocess")
                << "Replace (indirect): " << cur << " -> " << its->second
                << ", prevLit = " << prevLit << std::endl;
            visited[cur] = its->second;
            continue;
          }
        }
        else
        {
          bool currLit = prevLit;
          if (scur != cur)
          {
            currLit = d_cs->hasLiteral(scur);
            scur = rewrite(scur);
            Trace("lemma-inprocess-debug")
                << "Inprocess " << cur << " -> " << scur << std::endl;
            bool doReplace = false;
            switch (options().theory.lemmaInprocess)
            {
              case options::LemmaInprocessMode::FULL:
                doReplace = (scur.isConst() || currLit || !prevLit);
                break;
              case options::LemmaInprocessMode::LIGHT:
                doReplace = (scur.isConst() || (currLit && !prevLit));
                break;
              default: break;
            }
            if (doReplace)
            {
              if (options().theory.lemmaInprocessInferEqLit
                  && ((scur.isConst() || currLit) && prevLit))
              {
                // inferred they are equivalent? maybe should send clause here?
                Node eql = rewrite(scur.eqNode(cur));
                if (d_eqLitLemmas.find(eql) == d_eqLitLemmas.end())
                {
                  d_eqLitLemmas.insert(eql);
                  eqLitLemmas.emplace_back(eql);
                }
              }
              Trace("lemma-inprocess")
                  << "Replace: " << cur << " -> " << scur
                  << ", currLit = " << currLit << ", prevLit = " << prevLit
                  << std::endl;
              visited[cur] = scur;
              d_subsLitMap[scur] = scur;
              continue;
            }
          }
          d_subsLitMap[scur] = cur;
        }
        visited[cur] = cur;
      }
      continue;
    }
    visit.pop_back();
    if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
        ret = rewrite(ret);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(lem) != visited.end());
  Assert(!visited.find(lem)->second.isNull());
  Node ret = visited[lem];
  if (!eqLitLemmas.empty())
  {
    eqLitLemmas.emplace_back(ret);
    return nm->mkAnd(eqLitLemmas);
  }
  return ret;
}

}  // namespace prop
}  // namespace cvc5::internal
