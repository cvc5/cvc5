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
 * Rewrite database
 */

#include "theory/rewrite_db.h"

#include "expr/node_algorithm.h"
#include "rewriter/rewrites.h"
#include "theory/rewrite_db_term_process.h"

using namespace cvc5::kind;
using namespace cvc5::rewriter;

namespace cvc5 {
namespace theory {

RewriteDb::RewriteDb()
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
  rewriter::addRules(*this);
}

void RewriteDb::addRule(
    DslPfRule id, const std::vector<Node> fvs, Node a, Node b, Node cond)
{
  NodeManager* nm = NodeManager::currentNM();
  Node eq = a.eqNode(b);
  // we canonize left-to-right, hence we should traverse in the opposite
  // order, since we index based on conclusion, we make a dummy node here
  Node tmp = nm->mkNode(IMPLIES, eq, cond);
  // convert to internal
  Node tmpi = tmp;  // RewriteDbTermProcess::toInternal(tmp);

  // must canonize
  Trace("rewrite-db") << "Add rule " << id << ": " << cond << " => " << a
                      << " == " << b << std::endl;
  Node cr = d_canon.getCanonicalTerm(tmpi, false, false);

  Node condC = cr[1];
  std::vector<Node> conds;
  if (condC.getKind() == AND)
  {
    for (const Node& c : condC)
    {
      // should flatten in proof inference listing
      Assert(c.getKind() != AND);
      conds.push_back(c);
    }
  }
  else if (!condC.isConst())
  {
    conds.push_back(condC);
  }
  else if (!condC.getConst<bool>())
  {
    // skip those with false condition
    return;
  }
  // make as expected matching: top symbol of all conditions is equality
  // this means (not p) becomes (= p false), p becomes (= p true)
  for (size_t i = 0, nconds = conds.size(); i < nconds; i++)
  {
    if (conds[i].getKind() == NOT)
    {
      conds[i] = conds[i][0].eqNode(d_false);
    }
    else if (conds[i].getKind() != EQUAL)
    {
      conds[i] = conds[i].eqNode(d_true);
    }
  }
  // register side conditions?

  Node eqC = cr[0];
  Assert(eqC.getKind() == EQUAL);

  // add to discrimination tree
  Trace("proof-db-debug") << "Add (canonical) rule " << eqC << std::endl;
  d_mt.addTerm(eqC);

  // match to get canonical variables
  std::unordered_map<Node, Node> msubs;
  if (!expr::match(eq, eqC, msubs))
  {
    Assert(false);
  }
  std::unordered_map<Node, Node>::iterator its;
  std::vector<Node> ofvs;
  std::vector<Node> cfvs;
  for (const Node& v : fvs)
  {
    its = msubs.find(v);
    if (its != msubs.end())
    {
      ofvs.push_back(v);
      cfvs.push_back(its->second);
    }
    else
    {
      Notice() << "In DSL rule " << id << ", variable " << v << " is unused, dropping it" << std::endl;
    }
  }

  // initialize rule
  d_rewDbRule[id].init(id, ofvs, cfvs, conds, eqC);
  d_concToRules[eqC].push_back(id);
}

void RewriteDb::getMatches(Node eq, expr::NotifyMatch* ntm)
{
  d_mt.getMatches(eq, ntm);
}

const RewriteProofRule& RewriteDb::getRule(DslPfRule id) const
{
  std::map<DslPfRule, RewriteProofRule>::const_iterator it =
      d_rewDbRule.find(id);
  Assert(it != d_rewDbRule.end());
  return it->second;
}

const std::vector<DslPfRule>& RewriteDb::getRuleIdsForConclusion(Node eq) const
{
  std::map<Node, std::vector<DslPfRule> >::const_iterator it =
      d_concToRules.find(eq);
  if (it != d_concToRules.end())
  {
    return it->second;
  }
  return d_emptyVec;
}

}  // namespace theory
}  // namespace cvc5
