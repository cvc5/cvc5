/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Static learning of the lemmas that the keys and NOT NULL columns of tables
 * give.
 */

#include "theory/bags/table_facts_learner.h"

#include <algorithm>

#include "expr/node_algorithm.h"
#include "smt/env.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

TableFactsLearner::TableFactsLearner(Env& env)
    : EnvObj(env), d_reader(nodeManager(), env.getRewriter())
{
}

TableFactsLearner::~TableFactsLearner() {}

void TableFactsLearner::ppStaticLearn(TNode in, std::vector<TrustNode>& learned)
{
  if (addFact(in))
  {
    // a new fact applies to every term seen so far
    learnFor(d_terms, learned);
    return;
  }
  std::vector<Node> fresh;
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit{in};
  do
  {
    TNode cur = visit.back();
    visit.pop_back();
    if (!visited.insert(cur).second)
    {
      continue;
    }
    if (isCandidate(cur) && d_termSeen.insert(cur).second)
    {
      d_terms.push_back(cur);
      fresh.push_back(cur);
    }
    visit.insert(visit.end(), cur.begin(), cur.end());
  } while (!visit.empty());
  // a new term gets the facts seen so far
  learnFor(fresh, learned);
}

bool TableFactsLearner::addFact(TNode lit)
{
  TableFacts one;
  if (!d_reader.readTableFact(lit, one))
  {
    return false;
  }
  bool isNew = false;
  for (const auto& [table, keys] : one.d_keys)
  {
    std::vector<Node>& lits = d_factLits[table];
    if (std::find(lits.begin(), lits.end(), lit) != lits.end())
    {
      continue;
    }
    lits.push_back(lit);
    std::vector<std::set<uint32_t>>& all = d_facts.d_keys[table];
    all.insert(all.end(), keys.begin(), keys.end());
    isNew = true;
  }
  for (const auto& [table, cols] : one.d_notNull)
  {
    std::vector<Node>& lits = d_factLits[table];
    if (std::find(lits.begin(), lits.end(), lit) != lits.end())
    {
      continue;
    }
    lits.push_back(lit);
    d_facts.d_notNull[table].insert(cols.begin(), cols.end());
    isNew = true;
  }
  if (!isNew)
  {
    return true;
  }
  // The terms of a fact are never rewritten by it: the lemma would only
  // restate the fact.
  std::vector<TNode> visit{lit};
  do
  {
    TNode cur = visit.back();
    visit.pop_back();
    if (d_protected.insert(cur).second)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  d_cache.clear();
  d_rewriter = std::make_unique<BagsRewriter>(nodeManager(),
                                              d_env.getRewriter(),
                                              nullptr,
                                              logicInfo().isHigherOrder(),
                                              &d_facts);
  return true;
}

bool TableFactsLearner::isCandidate(const Node& t) const
{
  // a bag term, or an equality of bags: some rules that read a fact apply to
  // the equality of two queries only
  if (t.getNumChildren() == 0 || t.getKind() == Kind::LAMBDA
      || (t.getKind() == Kind::EQUAL && !t[0].getType().isBag())
      || d_env.theoryOf(t) != THEORY_BAGS)
  {
    return false;
  }
  return d_protected.find(t) == d_protected.end() && !expr::hasFreeVar(t);
}

Node TableFactsLearner::premiseOf(const Node& t) const
{
  std::unordered_set<Node> syms;
  expr::getSymbols(t, syms);
  std::vector<Node> lits;
  for (const auto& [table, tableLits] : d_factLits)
  {
    if (syms.find(table) == syms.end())
    {
      continue;
    }
    for (const Node& l : tableLits)
    {
      if (std::find(lits.begin(), lits.end(), l) == lits.end())
      {
        lits.push_back(l);
      }
    }
  }
  if (lits.empty())
  {
    return Node::null();
  }
  return nodeManager()->mkAnd(lits);
}

Node TableFactsLearner::rewriteWithFacts(const Node& n)
{
  auto it = d_cache.find(n);
  if (it != d_cache.end())
  {
    return it->second;
  }
  Node ret = rewriteWithFactsRec(n, 0);
  d_cache[n] = ret;
  return ret;
}

Node TableFactsLearner::rewriteWithFactsRec(const Node& n, size_t depth)
{
  // A bound on the nesting of the calls below: each follows a rule that read
  // a fact, and a chain of them this long would be a loop between the rules.
  const size_t maxDepth = 64;
  NodeManager* nm = nodeManager();
  std::unordered_map<Node, Node> visited;
  std::vector<Node> visit{n};
  do
  {
    Node cur = visit.back();
    visit.pop_back();
    auto it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.push_back(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    if (!it->second.isNull())
    {
      continue;
    }
    Node ret = cur;
    if (cur.getNumChildren() > 0)
    {
      bool changed = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& c : cur)
      {
        const Node& cn = visited[c];
        changed = changed || cn != c;
        children.push_back(cn);
      }
      if (changed)
      {
        ret = rewrite(nm->mkNode(cur.getKind(), children));
      }
      if (depth < maxDepth && ret.getNumChildren() > 0
          && ret.getKind() != Kind::LAMBDA
          && d_env.theoryOf(ret) == THEORY_BAGS)
      {
        // ret is in normal form for the rewriter of the theory, so only a
        // rule that reads a fact applies
        Node nr = d_rewriter->postRewrite(ret).d_node;
        if (nr != ret)
        {
          nr = rewrite(nr);
          ret = rewriteWithFactsRec(nr, depth + 1);
        }
      }
    }
    visited[cur] = ret;
  } while (!visit.empty());
  return visited[n];
}

void TableFactsLearner::learnFor(const std::vector<Node>& terms,
                                 std::vector<TrustNode>& learned)
{
  if (d_rewriter == nullptr)
  {
    return;
  }
  NodeManager* nm = nodeManager();
  for (const Node& t : terms)
  {
    if (d_protected.find(t) != d_protected.end())
    {
      continue;
    }
    Node tr = rewriteWithFacts(t);
    if (tr == t)
    {
      continue;
    }
    Node prem = premiseOf(t);
    if (prem.isNull())
    {
      continue;
    }
    Node eq = t.eqNode(tr);
    Node lem = nm->mkNode(Kind::IMPLIES, prem, eq);
    if (d_learned.insert(lem).second)
    {
      Trace("bags-table-facts") << "learned: " << lem << std::endl;
      learned.push_back(TrustNode::mkTrustLemma(lem, nullptr));
    }
  }
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
