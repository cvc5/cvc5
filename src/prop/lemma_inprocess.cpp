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
 * Learner for literals asserted at level zero.
 */

#include "prop/lemma_inprocess.h"

#include "expr/node_algorithm.h"
#include "prop/zero_level_learner.h"
#include "smt/env.h"

namespace cvc5::internal {
namespace prop {

LemmaInprocess::LemmaInprocess(Env& env, CnfStream* cs, ZeroLevelLearner& zll)
    : EnvObj(env),
      d_cs(cs),
      d_tsmap(zll.getSubstitutions()),
      d_tcpmap(zll.getConstantPropagations()), d_subsLitMap(userContext())
{
}
TrustNode LemmaInprocess::inprocessLemma(TrustNode& trn)
{
  const Node& proven = trn.getProven();
  Trace("ajr-temp") << "Process" << std::endl;
  Node provenp = processInternal(proven);
  Trace("ajr-temp") << "...finish" << std::endl;
  if (provenp != proven)
  {
    Trace("lemma-inprocess-lemma") << "Inprocess " << proven << " returns " << provenp << std::endl;
    // TODO: proofs
    return TrustNode::mkTrustNode(trn.getKind(), provenp);
  }
  return trn;
}

Node LemmaInprocess::processInternal(const Node& lem)
{
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
        scur = d_tcpmap.get().apply(scur, d_env.getRewriter());
        its = d_subsLitMap.find(scur);
        if (its!=d_subsLitMap.end())
        {
          if (cur!=its->second)
          {
            Trace("lemma-inprocess")
                << "Replace (indirect): " << cur << " -> " << its->second << ", prevLit = " << prevLit << std::endl;
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
            if (scur.isConst() || currLit || !prevLit)
            {
              if (prevLit)
              {
                // inferred they are equivalent? maybe should send clause here?
              }
              Trace("lemma-inprocess")
                  << "Replace: " << cur << " -> " << scur
                  << ", currLit = " << currLit << ", prevLit = " << prevLit << std::endl;
              visited[cur] = scur;
              d_subsLitMap[scur] = scur;
              continue;
            }
          }
          d_subsLitMap[cur] = cur;
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
  return visited[lem];
}

}  // namespace prop
}  // namespace cvc5::internal
