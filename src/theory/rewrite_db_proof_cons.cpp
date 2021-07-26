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
 * Rewrite database proof reconstructor
 */

#include "theory/rewrite_db_proof_cons.h"

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/node_algorithm.h"
#include "smt/smt_statistics_registry.h"
#include "theory/builtin/proof_checker.h"
#include "theory/rewrite_db_term_process.h"
#include "theory/rewriter.h"

using namespace cvc5::rewriter;
using namespace cvc5::kind;

namespace cvc5 {
namespace theory {

struct InflectionVarAttributeId
{
};
using InflectionVarAttribute = expr::Attribute<InflectionVarAttributeId, Node>;

RewriteDbProofCons::RewriteDbProofCons(RewriteDb* db, ProofNodeManager* pnm)
    : d_notify(*this),
      d_trrc(pnm),
      d_db(db),
      d_pnm(pnm),
      d_eval(),
      d_currRecLimit(0),
      d_currFixedPointId(DslPfRule::FAIL),
      d_statTotalInputs(smtStatisticsRegistry().registerInt(
          "RewriteDbProofCons::totalInputs")),
      d_statTotalAttempts(smtStatisticsRegistry().registerInt(
          "RewriteDbProofCons::totalAttempts"))
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

bool RewriteDbProofCons::prove(CDProof* cdp,
                               Node a,
                               Node b,
                               theory::TheoryId tid,
                               MethodId mid,
                               uint32_t recLimit)
{
  ++d_statTotalInputs;
  // clear the proof caches? use attributes instead?
  d_pcache.clear();
  // clear the evaluate cache?
  d_evalCache.clear();
  Trace("rpc") << "RewriteDbProofCons::prove: " << a << " == " << b
               << std::endl;
  Trace("rpc-debug") << "- prove basic" << std::endl;
  // first, try with the basic utility
  if (d_trrc.prove(cdp, a, b, tid, mid))
  {
    Trace("rpc") << "...success (basic)" << std::endl;
    return true;
  }
  Trace("rpc-debug") << "- convert to internal" << std::endl;
  DslPfRule id;
  Node eq = a.eqNode(b);
  Node eqi = d_rdnc.convert(eq);
  if (!proveInternalBase(eqi, id))
  {
    Trace("rpc-debug") << "- prove internal" << std::endl;
    // add one to recursion limit, since it is decremented whenever we initiate
    // the getMatches routine.
    d_currRecLimit = recLimit + 1;
    // Otherwise, we call the main prove internal method, which recurisvely
    // tries to find a matched conclusion whose conditions can be proven
    id = proveInternal(eqi);
    Trace("rpc-debug") << "- finished prove internal" << std::endl;
  }
  bool success = (id != DslPfRule::FAIL);
  // if a proof was provided, fill it in
  if (success && cdp != nullptr)
  {
    Trace("rpc-debug") << "- ensure proof" << std::endl;
    // if it changed encoding, account for this
    if (eq != eqi)
    {
      cdp->addStep(eq, PfRule::ENCODE_PRED_TRANSFORM, {eqi}, {eq});
    }
    ensureProofInternal(cdp, eqi);
    Assert(cdp->hasStep(eqi));
    Trace("rpc-debug") << "- finish ensure proof" << std::endl;
  }
  Trace("rpc") << "..." << (success ? "success" : "fail") << std::endl;
  return success;
}

DslPfRule RewriteDbProofCons::proveInternal(Node eqi)
{
  ++d_statTotalAttempts;
  // eqi should not hold trivially and should not be cached
  Assert(d_currRecLimit > 0);
  Trace("rpc-debug2") << "proveInternal " << eqi << std::endl;
  // Otherwise, call the get matches routine. This will call notifyMatch below
  // for each matching rewrite rule conclusion in the database
  // decrease the recursion depth
  Assert(eqi.getKind() == EQUAL);
  Node prevTarget = d_target;
  // TODO: first, try congruence if possible

  d_currRecLimit--;
  d_target = eqi;
  d_db->getMatches(eqi[0], &d_notify);
  d_target = prevTarget;
  d_currRecLimit++;
  // if we cached it during the above call, we succeeded
  std::unordered_map<Node, ProvenInfo>::iterator it = d_pcache.find(eqi);
  if (it != d_pcache.end())
  {
    Assert(it->second.d_id != DslPfRule::FAIL)
        << "unexpected failure for " << eqi;
    return it->second.d_id;
  }
  // store failure, and its maximum depth
  ProvenInfo& pi = d_pcache[eqi];
  pi.d_id = DslPfRule::FAIL;
  pi.d_failMaxDepth = d_currRecLimit;
  return DslPfRule::FAIL;
}

bool RewriteDbProofCons::notifyMatch(Node s,
                                     Node n,
                                     std::vector<Node>& vars,
                                     std::vector<Node>& subs)
{
  Assert(d_target.getKind() == EQUAL && d_target[0] == s);
  Assert(s.getType().isComparableTo(n.getType()));
  Assert(vars.size() == subs.size());
  Trace("rpc-debug2") << "notifyMatch: " << s << " from " << n << " via "
                      << vars << " -> " << subs << std::endl;
  if (d_currFixedPointId != DslPfRule::FAIL)
  {
    Trace("rpc-debug2") << "Part of fixed point for rule " << d_currFixedPointId
                        << std::endl;
    const RewriteProofRule& rpr = d_db->getRule(d_currFixedPointId);
    // get the conclusion
    Node target = rpr.getConclusion();
    // apply substitution, which may notice vars may be out of order wrt rule
    // var list
    target = expr::narySubstitute(target, vars, subs);
    // We now prove with the given rule. this should only fail if there are
    // conditions on the rule which fail. Notice we never allow recursion here.
    // We also don't permit inflection matching (which regardless should not
    // apply).
    if (proveWithRule(
            d_currFixedPointId, target, vars, subs, false, false, false))
    {
      // successfully proved, store in temporary variable
      d_currFixedPointConc = target;
    }
    // regardless, no further matches, due to semantics of fixed point which
    // limits to first match
    return false;
  }
  bool recurse = d_currRecLimit > 0;
  // get the rule identifiers for the conclusion
  const std::vector<DslPfRule>& ids = d_db->getRuleIdsForHead(n);
  Assert(!ids.empty());
  // check each rule instance, succeed if one proves
  for (DslPfRule id : ids)
  {
    Trace("rpc-debug2") << "Check rule " << id << std::endl;
    // try to prove target with the current rule, using inflection matching
    // and fixed point semantics
    if (proveWithRule(id, d_target, vars, subs, true, true, recurse))
    {
      // if successful, we do not want to be notified of further matches
      // and return false here.
      return false;
    }
    // notice that we do not cache a failure here since we only know that the
    // current rule was not able to prove the current target
  }
  // want to keep getting notify calls
  return true;
}

bool RewriteDbProofCons::proveWithRule(DslPfRule id,
                                       Node target,
                                       const std::vector<Node>& vars,
                                       const std::vector<Node>& subs,
                                       bool doInflectMatch,
                                       bool doFixedPoint,
                                       bool doRecurse)
{
  Assert(!target.isNull() && target.getKind() == EQUAL);
  const RewriteProofRule& rpr = d_db->getRule(id);
  // does it conclusion match what we are trying to show?
  Node conc = rpr.getConclusion();
  Assert(conc.getKind() == EQUAL && d_target.getKind() == EQUAL);
  // get rule conclusion, which may incorporate fixed point semantics when
  // doFixedPoint is true. This stores the rule for the conclusion in pic,
  // which is either id or DslPfRule::TRANS.
  ProvenInfo pic;
  Node stgt = getRuleConclusion(rpr, vars, subs, pic, doFixedPoint);
  std::vector<Node> iconds;
  Trace("rpc-debug2") << "            RHS: " << conc[1] << std::endl;
  Trace("rpc-debug2") << "Substituted RHS: " << stgt << std::endl;
  Trace("rpc-debug2") << "     Target RHS: " << target[1] << std::endl;
  // inflection substitution, used if conclusion does not exactly match
  std::unordered_map<Node, std::pair<Node, Node>> isubs;
  if (stgt != target[1])
  {
    if (!doInflectMatch)
    {
      Trace("rpc-debug2") << "...fail (no inflection)" << std::endl;
      return false;
    }
    // if not a perfect match, infer the (conditional) rule that would have
    // matched
    Node irhs = inflectMatch(conc[1], target[1], vars, subs, isubs);
    if (irhs.isNull())
    {
      Trace("rpc-debug2") << "...fail (inflection match)" << std::endl;
      return false;
    }
    Trace("rpc-debug2") << "Would have succeeded with rule: " << std::endl;
    // the variables / substitution we will use to generate constraints below
    std::vector<Node> uvars;
    std::vector<Node> usubs;
    if (pic.usedFixPoint())
    {
      // use the substitution of the last proven equality, which determines
      // what the generated inflection conditions are
      Node lastEq = pic.d_vars.back();
      ProvenInfo& pile = d_pcache[lastEq];
      Assert(pile.d_id == id);
      uvars = pile.d_vars;
      usubs = pile.d_subs;
    }
    else
    {
      uvars = vars;
      usubs = subs;
    }
    std::vector<Node> conds;
    for (const std::pair<const Node, std::pair<Node, Node>>& i : isubs)
    {
      Node eq = i.first.eqNode(i.second.first);
      conds.push_back(eq);
      // orient: target comes second
      Node seq = expr::narySubstitute(i.second.first, uvars, usubs)
                     .eqNode(i.second.second);
      iconds.push_back(seq);
      Trace("rpc-debug2") << eq << " ";
    }
    Trace("rpc-debug2") << "=> (" << irhs << " == " << conc[0] << ")"
                        << std::endl;
    Trace("rpc-debug2") << "Inflection conditions: " << iconds << std::endl;
  }
  // do its conditions hold?
  // Get the conditions, substituted { vars -> subs } and with side conditions
  // evaluated.
  std::vector<Node> vcs;
  // add inflection conditions
  vcs.insert(vcs.begin(), iconds.begin(), iconds.end());
  if (!rpr.getObligations(vars, subs, vcs))
  {
    // cannot get conditions, likely due to failed side condition
    Trace("rpc-debug2") << "...fail (obligations)" << std::endl;
    return false;
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
        Trace("rpc-debug2")
            << "...fail (simple condition failure)" << std::endl;
        return false;
      }
      // already holds, continue
      continue;
    }
    if (!doRecurse)
    {
      // we can't apply recursion, return false
      Trace("rpc-debug2") << "...fail (recursion limit)" << std::endl;
      return false;
    }
    // save, to check below
    condToProve.push_back(cond);
  }
  // if no trivial failures, go back and try to recursively prove
  for (const Node& cond : condToProve)
  {
    Trace("rpc-infer-sc") << "Check condition: " << cond << std::endl;
    // recursively check if the condition holds
    DslPfRule cid = proveInternal(cond);
    if (cid == DslPfRule::FAIL)
    {
      // print reason for failure
      Trace("rpc-infer-debug")
          << "required: " << cond << " for " << rpr.getName() << std::endl;
      return false;
    }
  }
  // successfully found instance of rule
  if (Trace.isOn("rpc-infer"))
  {
    Trace("rpc-infer") << "INFER " << target << " by " << rpr.getName()
                       << std::endl;
  }
  // cache the success
  ProvenInfo& pi = d_pcache[target];
  pi.d_id = pic.d_id;
  if (pic.usedFixPoint())
  {
    pi.d_vars = pic.d_vars;
  }
  else
  {
    pi.d_vars = vars;
    pi.d_subs = subs;
  }
  pi.d_iconds = iconds;
  // success
  return true;
}

bool RewriteDbProofCons::proveInternalBase(Node eqi, DslPfRule& idb)
{
  Assert(eqi.getKind() == kind::EQUAL);
  // already cached?
  std::unordered_map<Node, ProvenInfo>::iterator it = d_pcache.find(eqi);
  if (it != d_pcache.end())
  {
    if (it->second.d_id != DslPfRule::FAIL)
    {
      // proof exists, return
      idb = it->second.d_id;
      return true;
    }
    if (d_currRecLimit <= it->second.d_failMaxDepth)
    {
      idb = it->second.d_id;
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
    ProvenInfo& pi = d_pcache[eqi];
    idb = DslPfRule::REFL;
    pi.d_id = idb;
    return true;
  }
  // evaluate the two sides of the equality, without help of the rewriter
  Node ev[2];
  for (size_t i = 0; i < 2; i++)
  {
    ev[i] = doEvaluate(eqi[i]);
    if (ev[i].isNull())
    {
      // does not evaluate
      // If it rewrites to false, then it is obviously infeasible. Notice that
      // rewriting is more expensive than evaluation, so we do it as a second
      // resort.
      Node lhs = i == 1 ? ev[0] : eqi[0];
      Node eqr = Rewriter::rewrite(lhs.eqNode(eqi[1]));
      if (eqr.isConst())
      {
        // definitely not true
        if (!eqr.getConst<bool>())
        {
          ProvenInfo& pi = d_pcache[eqi];
          Trace("rpc-debug2") << "Infeasible due to rewriting: " << eqi[0]
                              << " == " << eqi[1] << std::endl;
          idb = DslPfRule::FAIL;
          pi.d_failMaxDepth = 0;
          pi.d_id = idb;
          return true;
        }
        // NOTE: if does not rewrite to true, it still could be true, hence we
        // fail
      }
      return false;
    }
  }
  ProvenInfo& pi = d_pcache[eqi];
  // we can evaluate both sides, check to see if the values are the same
  if (ev[0] == ev[1])
  {
    idb = DslPfRule::EVAL;
  }
  else
  {
    idb = DslPfRule::FAIL;
    // failure relies on nothing, depth is 0
    pi.d_failMaxDepth = 0;
  }
  // cache it
  pi.d_id = idb;
  return true;
}

bool RewriteDbProofCons::ensureProofInternal(CDProof* cdp, Node eqi)
{
  // TODO: use single internal cdp to improve subproof sharing?
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, bool> visited;
  std::unordered_map<TNode, std::vector<Node>> premises;
  std::unordered_map<TNode, std::vector<Node>> pfArgs;
  std::unordered_map<TNode, bool>::iterator it;
  std::unordered_map<Node, ProvenInfo>::iterator itd;
  std::vector<Node>::iterator itv;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(eqi);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    itd = d_pcache.find(cur);
    Assert(cur.getKind() == kind::EQUAL);
    if (it == visited.end())
    {
      Trace("rpc-debug") << "Ensure proof for " << cur << std::endl;
      visit.push_back(cur);
      // may already have a proof rule from a previous call
      if (cdp->hasStep(cur))
      {
        visited[cur] = true;
      }
      else
      {
        Assert(itd != d_pcache.end());
        Assert(itd->second.d_id != DslPfRule::FAIL);
        if (itd->second.d_id == DslPfRule::REFL)
        {
          // trivial proof
          Assert(cur[0] == cur[1]);
          cdp->addStep(cur, PfRule::REFL, {}, {cur[0]});
        }
        else if (itd->second.d_id == DslPfRule::EVAL)
        {
          visited[cur] = true;
          // NOTE: this could just evaluate the equality itself
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
            cdp->addStep(eq, PfRule::EVALUATE, {}, {cur[i]});
          }
          if (transc.size() == 2)
          {
            // do transitivity if both sides evaluate
            cdp->addStep(cur, PfRule::TRANS, transc, {});
          }
        }
        else
        {
          visited[cur] = false;
          std::vector<Node>& ps = premises[cur];
          if (itd->second.usedFixPoint())
          {
            // premises are the steps, stored in d_vars
            ps.insert(premises[cur].end(),
                      itd->second.d_vars.begin(),
                      itd->second.d_vars.end());
          }
          else
          {
            const RewriteProofRule& rpr = d_db->getRule(itd->second.d_id);
            // add the DSL proof rule we used
            pfArgs[cur].push_back(
                nm->mkConst(Rational(static_cast<uint32_t>(itd->second.d_id))));
            // compute premises based on the used substitution
            // build the substitution context
            const std::vector<Node>& vs = rpr.getVarList();
            Assert(itd->second.d_vars.size() == vs.size());
            std::vector<Node> rsubs;
            // must order the variables to match order of rewrite rule
            for (const Node& v : vs)
            {
              itv = std::find(
                  itd->second.d_vars.begin(), itd->second.d_vars.end(), v);
              size_t d = std::distance(itd->second.d_vars.begin(), itv);
              Assert(d < itd->second.d_subs.size());
              rsubs.push_back(itd->second.d_subs[d]);
            }
            // get the conditions, store into premises of cur.
            if (!rpr.getObligations(vs, rsubs, ps))
            {
              Assert(false);
              // failed a side condition?
              return false;
            }
            pfArgs[cur].insert(pfArgs[cur].end(), rsubs.begin(), rsubs.end());
          }
          // recurse on premises
          visit.insert(visit.end(), ps.begin(), ps.end());
          // recurse on inflection conditions
          visit.insert(visit.end(),
                       itd->second.d_iconds.begin(),
                       itd->second.d_iconds.end());
        }
      }
    }
    else if (!it->second)
    {
      // Now, add the proof rule. We do this after its children proofs already
      // exist.
      visited[cur] = true;
      Assert(premises.find(cur) != premises.end());
      std::vector<Node>& ps = premises[cur];
      Assert(pfArgs.find(cur) != pfArgs.end());
      // get the conclusion
      Node conc;
      if (itd->second.usedFixPoint())
      {
        conc = ps[0][0].eqNode(ps.back()[1]);
        cdp->addStep(conc, PfRule::TRANS, ps, {});
      }
      else
      {
        const RewriteProofRule& rpr = d_db->getRule(itd->second.d_id);
        const std::vector<Node>& args = pfArgs[cur];
        std::vector<Node> subs(args.begin() + 1, args.end());
        conc = rpr.getConclusionFor(subs);
        Trace("rpc-debug") << "Finalize proof for " << cur << std::endl;
        Trace("rpc-debug") << "Proved: " << cur << std::endl;
        Trace("rpc-debug") << "From: " << conc << std::endl;
        Trace("rpc-debug") << "Used inflection conditions: "
                           << itd->second.d_iconds << std::endl;
        cdp->addStep(conc, PfRule::DSL_REWRITE, ps, args);
      }
      // if we had inflection conditions, we need to also use a skeleton
      if (!itd->second.d_iconds.empty())
      {
        Assert(cur[1] != conc[1]);
        Node eqk = conc[1].eqNode(cur[1]);
        Trace("rpc-debug") << "Prove skeleton: " << eqk << std::endl;
        ensureProofSkeletonInternal(cdp, conc[1], cur[1]);
        cdp->addStep(cur, PfRule::TRANS, {conc, eqk}, {});
      }
    }
  } while (!visit.empty());
  return true;
}
void RewriteDbProofCons::ensureProofSkeletonInternal(CDProof* cdp,
                                                     Node a,
                                                     Node b)
{
  std::unordered_map<std::pair<TNode, TNode>, bool, TNodePairHashFunction>
      visited;
  std::unordered_map<std::pair<TNode, TNode>, bool, TNodePairHashFunction>::
      iterator it;
  std::unordered_map<Node, Node>::iterator subsIt;

  std::vector<std::pair<TNode, TNode>> stack;
  stack.emplace_back(a, b);
  std::pair<TNode, TNode> curr;

  while (!stack.empty())
  {
    curr = stack.back();
    stack.pop_back();
    it = visited.find(curr);
    if (it == visited.end())
    {
      visited[curr] = true;
      if (curr.first == curr.second)
      {
        Node eq = curr.first.eqNode(curr.second);
        Trace("rpc-debug") << "Add refl step " << eq << std::endl;
        // holds trivially, add REFL
        cdp->addStep(eq, PfRule::REFL, {}, {curr.first});
      }
      else if (curr.first.getNumChildren() > 0)
      {
        if (curr.first.getNumChildren() == curr.second.getNumChildren()
            && curr.first.getOperator() == curr.second.getOperator())
        {
          visited[curr] = false;
          stack.push_back(curr);
          // recurse on children
          for (size_t i = 0, n = curr.first.getNumChildren(); i < n; ++i)
          {
            stack.emplace_back(curr.first[i], curr.second[i]);
          }
        }
        // otherwise, equality should be proven already
      }
      // otherwise the two terms do not match, and the equality should be proven
      // already
    }
    else if (!it->second)
    {
      // we match due to children, thus, congruence
      Assert(curr.first.getNumChildren() > 0);
      Assert(curr.first.getOperator() == curr.second.getOperator());
      Assert(curr.first.getNumChildren() == curr.second.getNumChildren());
      std::vector<Node> childPf;
      for (size_t i = 0, nchild = curr.first.getNumChildren(); i < nchild; i++)
      {
        childPf.push_back(curr.first[i].eqNode(curr.second[i]));
      }
      std::vector<Node> argsPf;
      argsPf.push_back(ProofRuleChecker::mkKindNode(curr.first.getKind()));
      if (curr.first.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        argsPf.push_back(curr.first.getOperator());
      }
      Node eq = curr.first.eqNode(curr.second);
      Trace("rpc-debug") << "Add cong step " << eq << std::endl;
      cdp->addStep(
          curr.first.eqNode(curr.second), PfRule::CONG, childPf, argsPf);
    }
  }
}

Node RewriteDbProofCons::doEvaluate(Node n)
{
  std::unordered_map<Node, Node>::iterator itv = d_evalCache.find(n);
  if (itv != d_evalCache.end())
  {
    return itv->second;
  }
  Node nev = d_eval.eval(n, {}, {}, false);
  d_evalCache[n] = nev;
  return nev;
}

Node RewriteDbProofCons::getRuleConclusion(const RewriteProofRule& rpr,
                                           const std::vector<Node>& vars,
                                           const std::vector<Node>& subs,
                                           ProvenInfo& pi,
                                           bool doFixedPoint)
{
  pi.d_id = rpr.getId();
  Node conc = rpr.getConclusion();
  // if fixed point, we continue applying
  if (doFixedPoint && rpr.isFixedPoint())
  {
    Assert(d_currFixedPointId == DslPfRule::FAIL);
    Assert(d_currFixedPointConc.isNull());
    d_currFixedPointId = rpr.getId();
    // check if stgt also rewrites with the same rule?
    bool continueFixedPoint;
    std::vector<Node> transEq;
    // start from the source, match again to start the chain. Notice this is
    // required for uniformity since we want to successfully cache the first
    // step, independent of the target.
    Node ssrc = expr::narySubstitute(conc[0], vars, subs);
    Node stgt = ssrc;
    do
    {
      continueFixedPoint = false;
      rpr.getMatches(stgt, &d_notify);
      if (!d_currFixedPointConc.isNull())
      {
        // currently avoid accidental loops: arbitrarily bound to 1000
        continueFixedPoint = transEq.size() <= 1000;
        Assert(d_currFixedPointConc.getKind() == EQUAL);
        transEq.push_back(stgt.eqNode(d_currFixedPointConc[1]));
        stgt = d_currFixedPointConc[1];
      }
      d_currFixedPointConc = Node::null();
    } while (continueFixedPoint);
    d_currFixedPointId = DslPfRule::FAIL;
    // add the transistivity rule here if needed
    if (transEq.size() >= 2)
    {
      pi.d_id = DslPfRule::TRANS;
      // store transEq in d_vars
      pi.d_vars = transEq;
    }
    // return the end of the chain, which will be used for constrained matching
    return stgt;
  }
  return expr::narySubstitute(conc[1], vars, subs);
}

Node RewriteDbProofCons::inflectMatch(
    Node n,
    Node s,
    const std::vector<Node>& vars,
    const std::vector<Node>& subs,
    std::unordered_map<Node, std::pair<Node, Node>>& isubs)
{
  Trace("rpc-inflect") << "InflectMatch " << n << " == " << s << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  BoundVarManager* bvm = nm->getBoundVarManager();
  std::unordered_map<std::pair<TNode, TNode>, Node, TNodePairHashFunction>
      visited;
  std::unordered_map<std::pair<TNode, TNode>, Node, TNodePairHashFunction>::
      iterator it;
  std::vector<Node>::const_iterator itv;

  std::unordered_map<TypeNode, size_t> inflectCounter;

  std::vector<std::pair<TNode, TNode>> stack;
  std::pair<TNode, TNode> init(n, s);
  stack.push_back(init);
  std::pair<TNode, TNode> curr;

  while (!stack.empty())
  {
    curr = stack.back();
    stack.pop_back();
    if (curr.first == curr.second)
    {
      visited[curr] = curr.first;
      // holds trivially
      continue;
    }
    it = visited.find(curr);
    if (it == visited.end())
    {
      bool matchSuccess = true;
      if (curr.first.getNumChildren() == 0)
      {
        // if the two subterms are not equal and the first one is a bound
        // variable...
        if (curr.first.getKind() == kind::BOUND_VARIABLE)
        {
          // the inflected form of n is itself
          visited[curr] = curr.first;
          // and we have not seen this variable before...
          itv = std::find(vars.begin(), vars.end(), curr.first);
          Assert(itv != vars.end());
          size_t d = std::distance(vars.begin(), itv);
          Assert(d < subs.size());
          // if we saw this variable before, make sure that (now and before) it
          // maps to the same subterm
          if (curr.second != subs[d])
          {
            matchSuccess = false;
            // visited[curr] will be overwritten below
          }
        }
        else
        {
          // the two subterms are not equal
          matchSuccess = false;
        }
      }
      else
      {
        // if the two subterms are not equal, make sure that their operators are
        // equal
        // we compare operators instead of kinds because different terms may
        // have the same kind (both `(id x)` and `(square x)` have kind
        // APPLY_UF) since many builtin operators like `PLUS` allow arbitrary
        // number of arguments, we also need to check if the two subterms have
        // the same number of children
        if (curr.first.getNumChildren() != curr.second.getNumChildren()
            || curr.first.getOperator() != curr.second.getOperator())
        {
          // TODO: (+ a b c) could match (+ a d) with constraint (= (+ b c) d)
          matchSuccess = false;
        }
        else
        {
          // recurse on children
          visited[curr] = Node::null();
          stack.push_back(curr);
          for (size_t i = 0, nc = curr.first.getNumChildren(); i < nc; ++i)
          {
            // eagerly check type constraints, which is important for cases
            // like (select A x) (select B s) where A and B are arrays with
            // the same element type but different index types.
            if (!curr.first[i].getType().isComparableTo(
                    curr.second[i].getType()))
            {
              matchSuccess = false;
              stack.resize(stack.size() - i - 1);
              // visited[curr] will be overwritten below
              break;
            }
            stack.emplace_back(curr.first[i], curr.second[i]);
          }
        }
      }
      if (!matchSuccess)
      {
        // failed to match
        // if they are definitely equal, return null now
        if (curr.first.isConst() && curr.second.isConst())
        {
          Assert(curr.first != curr.second);
          return Node::null();
        }
        TypeNode tn = curr.first.getType();
        size_t inflectId = inflectCounter[tn];
        // variables are unique to (id, type id)
        Node idn = nm->mkConst(Rational(inflectId));
        size_t typeId = getOrAssignTypeId(tn);
        Node idt = nm->mkConst(Rational(typeId));
        Node cval = BoundVarManager::getCacheValue(idn, idt);
        Node v = bvm->mkBoundVar<InflectionVarAttribute>(cval, tn);
        Trace("rpc-inflect")
            << "- inflect " << curr.first << " == " << curr.second << " via "
            << v << std::endl;
        inflectCounter[tn]++;
        visited[curr] = v;
        isubs[v] = curr;
      }
    }
    else if (it->second.isNull())
    {
      // reconstruct
      Node ret = curr.first;
      bool childChanged = false;
      std::vector<Node> children;
      if (curr.first.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(curr.first.getOperator());
      }
      for (size_t i = 0, nc = curr.first.getNumChildren(); i < nc; ++i)
      {
        std::pair<TNode, Node> key(curr.first[i], curr.second[i]);
        it = visited.find(key);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || curr.first[i] != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(curr.first.getKind(), children);
      }
      visited[curr] = ret;
    }
  }
  AlwaysAssert(visited.find(init) != visited.end());
  AlwaysAssert(!visited.find(init)->second.isNull());
  return visited[init];
}

size_t RewriteDbProofCons::getOrAssignTypeId(TypeNode tn)
{
  std::map<TypeNode, size_t>::iterator it = d_typeId.find(tn);
  if (it != d_typeId.end())
  {
    return it->second;
  }
  size_t id = d_typeId.size();
  d_typeId[tn] = id;
  return id;
}

}  // namespace theory
}  // namespace cvc5
