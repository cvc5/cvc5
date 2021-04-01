/*********************                                                        */
/*! \file rewrite_db_proof_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewrite database proof generator
 **/

#include "theory/rewrite_db_proof_generator.h"

#include "expr/node_algorithm.h"
#include "theory/builtin/proof_checker.h"
#include "theory/rewrite_db_term_process.h"

namespace cvc5 {
namespace theory {

RewriteDbProofCons::RewriteDbProofCons(RewriteDb& db, ProofNodeManager* pnm)
    : d_notify(*this), d_db(db), d_eval(), d_proof(pnm), d_currRecLimit(0)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

bool RewriteDbProofCons::prove(Node a,
                               Node b,
                               unsigned recLimit,
                               bool ensureProof)
{
  DslPfRule id;
  Node eq = a.eqNode(b);
  Node eqi = RewriteDbTermProcess::toInternal(eq);
  if (!proveInternalBase(eqi, id))
  {
    // add one to recursion limit, since it is decremented whenever we initiate
    // the getMatches routine.
    d_currRecLimit = recLimit + 1;
    // Otherwise, we call the main prove internal method, which recurisvely
    // tries to find a matched conclusion whose conditions can be proven
    id = proveInternal(eqi);
  }
  // clear the proof caches? use attributes instead?
  d_pcache.clear();
  d_pcacheFailMaxDepth.clear();
  bool success = (id != DslPfRule::FAIL);
  if (success && ensureProof)
  {
    // ensure proof exists
    ensureProofInternal(eqi);
    Assert(d_proof.hasStep(eqi));
  }
  // clear the evaluate cache?
  d_evalCache.clear();
  return success;
}

std::string RewriteDbProofCons::identify() const
{
  return "RewriteDbProofCons";
}

DslPfRule RewriteDbProofCons::proveInternal(Node eqi)
{
  // eqi should not hold trivially and should not be cached
  Assert(d_currRecLimit > 0);
  // Otherwise, call the get matches routine. This will call notifyMatch below
  // for each matching rewrite rule conclusion in the database
  // decrease the recursion depth
  d_currRecLimit--;
  d_db.getMatches(eqi, &d_notify);
  d_currRecLimit++;
  // if we cached it during the above call, we succeeded
  std::unordered_map<Node, DslPfRule, NodeHashFunction>::iterator it =
      d_pcache.find(eqi);
  if (it != d_pcache.end())
  {
    Assert(it->second != DslPfRule::FAIL);
    return it->second;
  }
  // store failure, and its maximum depth
  d_pcache[eqi] = DslPfRule::FAIL;
  d_pcacheFailMaxDepth[eqi] = d_currRecLimit;
  return DslPfRule::FAIL;
}

bool RewriteDbProofCons::notifyMatch(Node s,
                                     Node n,
                                     std::vector<Node>& vars,
                                     std::vector<Node>& subs)
{
  Assert(s.getType().isComparableTo(n.getType()));
  Assert(vars.size() == subs.size());
  // get the rule identifiers for the conclusion
  const std::vector<DslPfRule>& ids = d_db.getRuleIdsForConclusion(n);
  Assert(!ids.empty());
  // check each rule instance, succeed if one proves
  bool recurse = d_currRecLimit > 0;
  for (DslPfRule id : ids)
  {
    const RewriteProofRule& rpr = d_db.getRule(id);
    // do its conditions hold?
    bool condSuccess = true;
    Trace("rew-db") << "Check rule " << rpr.getName() << std::endl;
    if (!recurse && rpr.hasConditions())
    {
      // can't recurse and has conditions, continue
      continue;
    }
    // Get the conditions, substituted { vars -> subs } and with side conditions
    // evaluated.
    std::vector<Node> vcs;
    if (!rpr.getConditions(vars, subs, vcs))
    {
      // cannot get conditions, likely due to failed side condition
      continue;
    }

    // First, check which premises are non-trivial, and if there is a trivial
    // failure. Those that are non-trivial are added to condToProve.
    std::vector<Node> condToProve;
    for (const Node& cond : vcs)
    {
      Assert(cond.getKind() == kind::EQUAL);
      // substitute to get the condition-to-prove
      DslPfRule cid;
      // check whether condition is already known to hold or not hold
      if (proveInternalBase(cond, cid))
      {
        if (cid == DslPfRule::FAIL)
        {
          // does not hold, we fail
          condSuccess = false;
          break;
        }
        // already holds, continue
        continue;
      }
      // save, to check below
      condToProve.push_back(cond);
    }
    if (condSuccess)
    {
      // if no trivial failures, go back and try to recursively prove
      for (const Node& cond : condToProve)
      {
        Trace("rew-db-infer-sc") << "Check condition: " << cond << std::endl;
        // recursively check if the condition holds
        DslPfRule cid = proveInternal(cond);
        if (cid == DslPfRule::FAIL)
        {
          // print reason for failure
          Trace("rew-db") << "required: " << cond << " for " << rpr.getName()
                          << std::endl;
          condSuccess = false;
          break;
        }
      }
      if (condSuccess)
      {
        // successfully found instance of rule
        if (Trace.isOn("rew-db-infer"))
        {
          Node se = RewriteDbTermProcess::toExternal(s);
          Trace("rew-db-infer")
              << "INFER " << se << " by " << rpr.getName() << std::endl;
        }
        d_pcache[s] = id;
        // don't need to notify any further matches, we are done
        return false;
      }
    }
  }
  // want to keep getting notify calls
  return true;
}

bool RewriteDbProofCons::proveInternalBase(Node eqi, DslPfRule& idb)
{
  Assert(eqi.getKind() == kind::EQUAL);
  // already cached?
  std::unordered_map<Node, DslPfRule, NodeHashFunction>::iterator it =
      d_pcache.find(eqi);
  if (it != d_pcache.end())
  {
    if (it->second != DslPfRule::FAIL)
    {
      // proof exists, return
      idb = it->second;
      return true;
    }
    Assert(d_pcacheFailMaxDepth.find(eqi) != d_pcacheFailMaxDepth.end());
    if (d_currRecLimit <= d_pcacheFailMaxDepth[eqi])
    {
      idb = it->second;
      return true;
    }
    // Will not succeed below, since we know we've already tried. Hence, we
    // are in a situation where we have yet to succeed to prove eqi for some
    // depth, but we are currently trying at a higher maximum depth.
    return false;
  }
  // symmetry or reflexivity, applied potentially to non-Booleans?
  // if (CDProof::isSame(eqi[0], eqi[1]))
  if (eqi[0] == eqi[1])
  {
    idb = DslPfRule::REFL;
    d_pcache[eqi] = idb;
    return true;
  }
  // evaluate the two sides of the equality, without help of the rewriter
  Node aev = doEvaluate(eqi[0]);
  if (aev.isNull())
  {
    // does not evaluate
    return false;
  }
  Node bev = doEvaluate(eqi[1]);
  if (bev.isNull())
  {
    // does not evaluate
    return false;
  }
  // we can evaluate both sides, check to see if the values are the same
  if (aev == bev)
  {
    idb = DslPfRule::EVAL;
  }
  else
  {
    idb = DslPfRule::FAIL;
    // failure relies on nothing, depth is 0
    d_pcacheFailMaxDepth[eqi] = 0;
  }
  // cache it
  d_pcache[eqi] = idb;
  return true;
}

bool RewriteDbProofCons::ensureProofInternal(Node eqi)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::unordered_map<TNode, std::vector<Node>, TNodeHashFunction> premises;
  std::unordered_map<TNode, bool, TNodeHashFunction>::iterator it;
  std::unordered_map<Node, DslPfRule, NodeHashFunction>::iterator itd;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(eqi);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    Assert(cur.getKind() == kind::EQUAL);
    if (it == visited.end())
    {
      visit.push_back(cur);
      // may already have a proof rule from a previous call
      if (d_proof.hasStep(cur))
      {
        visited[cur] = true;
      }
      else
      {
        itd = d_pcache.find(cur);
        Assert(itd != d_pcache.end());
        Assert(itd->second != DslPfRule::FAIL);
        if (itd->second == DslPfRule::REFL)
        {
          // trivial proof
          Assert(cur[0] == cur[1]);
          d_proof.addStep(cur, PfRule::REFL, {}, {cur[0]});
        }
        else if (itd->second == DslPfRule::EVAL)
        {
          visited[cur] = true;
          Assert(cur.getKind() == kind::EQUAL);
          std::vector<Node> transc;
          for (unsigned i = 0; i < 2; i++)
          {
            Node curv = doEvaluate(cur[i]);
            if (curv == cur[i])
            {
              continue;
            }
            Node eq = cur[i].eqNode(curv);
            // flip orientation for second child
            transc.push_back(i == 1 ? curv.eqNode(cur[i]) : eq);
            // trivial evaluation, add evaluation method id
            d_proof.addStep(eq, PfRule::EVALUATE, {}, {cur[i]});
          }
          if (transc.size() == 2)
          {
            // do transitivity if both sides evaluate
            d_proof.addStep(cur, PfRule::TRANS, transc, {});
          }
        }
        else
        {
          visited[cur] = false;
          const RewriteProofRule& rpr = d_db.getRule(itd->second);
          // compute premises based on the used substitution
          std::unordered_map<Node, Node, NodeHashFunction> subs;
          if (!expr::match(rpr.getConclusion(), cur, subs))
          {
            Assert(false);
            return false;
          }
          // build the substitution context
          std::vector<Node> vs;
          std::vector<Node> ss;
          for (const std::pair<const Node, Node>& sp : subs)
          {
            vs.push_back(sp.first);
            ss.push_back(sp.second);
          }
          // get the conditions, store into premises of cur.
          if (!rpr.getConditions(vs, ss, premises[cur]))
          {
            Assert(false);
            // failed a side condition?
            return false;
          }
        }
      }
    }
    else if (!it->second)
    {
      // Now, add the proof rule. We do this after its children proofs already
      // exist.
      visited[cur] = true;
      std::vector<Node> pfArgs;
      pfArgs.push_back(
          nm->mkConst(Rational(static_cast<uint32_t>(itd->second))));
      pfArgs.push_back(cur);
      d_proof.addStep(cur, PfRule::DSL_REWRITE, premises[cur], pfArgs);
    }
  } while (!visit.empty());
  return true;
}

Node RewriteDbProofCons::doEvaluate(Node n)
{
  std::unordered_map<Node, Node, NodeHashFunction>::iterator itv =
      d_evalCache.find(n);
  if (itv != d_evalCache.end())
  {
    return itv->second;
  }
  Node nev = d_eval.eval(n, {}, {}, false);
  d_evalCache[n] = nev;
  return nev;
}

}  // namespace theory
}  // namespace cvc5
