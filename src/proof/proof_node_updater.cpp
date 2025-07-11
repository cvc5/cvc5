/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Hans-Joerg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of a utility for updating proof nodes.
 */

#include "proof/proof_node_updater.h"

#include "proof/lazy_proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_ensure_closed.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"

namespace cvc5::internal {

ProofNodeUpdaterCallback::ProofNodeUpdaterCallback() {}
ProofNodeUpdaterCallback::~ProofNodeUpdaterCallback() {}

bool ProofNodeUpdaterCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                            const std::vector<Node>& fa,
                                            bool& continueUpdate)
{
  return false;
}

bool ProofNodeUpdaterCallback::update(Node res,
                                      ProofRule id,
                                      const std::vector<Node>& children,
                                      const std::vector<Node>& args,
                                      CDProof* cdp,
                                      bool& continueUpdate)
{
  return false;
}

bool ProofNodeUpdaterCallback::shouldUpdatePost(std::shared_ptr<ProofNode> pn,
                                                const std::vector<Node>& fa)
{
  return false;
}

bool ProofNodeUpdaterCallback::updatePost(Node res,
                                          ProofRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args,
                                          CDProof* cdp)
{
  return false;
}

void ProofNodeUpdaterCallback::finalize(std::shared_ptr<ProofNode> pn)
{
  // do nothing
}

ProofNodeUpdater::ProofNodeUpdater(Env& env,
                                   ProofNodeUpdaterCallback& cb,
                                   bool mergeSubproofs,
                                   bool autoSym)
    : EnvObj(env),
      d_cb(cb),
      d_debugFreeAssumps(false),
      d_mergeSubproofs(mergeSubproofs),
      d_autoSym(autoSym)
{
}

void ProofNodeUpdater::process(std::shared_ptr<ProofNode> pf)
{
  if (d_debugFreeAssumps)
  {
    if (TraceIsOn("pfnu-debug"))
    {
      Trace("pfnu-debug2") << "Initial proof: " << *pf.get() << std::endl;
      Trace("pfnu-debug") << "ProofNodeUpdater::process" << std::endl;
      Trace("pfnu-debug") << "Expected free assumptions: " << std::endl;
      for (const Node& fa : d_freeAssumps)
      {
        Trace("pfnu-debug") << "- " << fa << std::endl;
      }
      std::vector<Node> assump;
      expr::getFreeAssumptions(pf.get(), assump);
      Trace("pfnu-debug") << "Current free assumptions: " << std::endl;
      for (const Node& fa : assump)
      {
        Trace("pfnu-debug") << "- " << fa << std::endl;
      }
    }
  }
  processInternal(pf, d_freeAssumps);
}

void ProofNodeUpdater::processInternal(std::shared_ptr<ProofNode> pf,
                                       std::vector<Node>& fa)
{
  // Note that processInternal uses a single scope; fa is updated based on
  // the current free assumptions of the proof nodes on the stack.

  // The list of proof nodes we are currently traversing beneath. This is used
  // for checking for cycles in the overall proof.
  std::vector<std::shared_ptr<ProofNode>> traversing;
  // Map from formulas to (closed) proof nodes that prove that fact
  std::map<Node, std::shared_ptr<ProofNode>> resCache;
  // Map from formulas to non-closed proof nodes that prove that fact. These
  // are replaced by proofs in the above map when applicable.
  std::map<Node, std::vector<std::shared_ptr<ProofNode>>> resCacheNcWaiting;
  // Map from proof nodes to whether they contain assumptions
  std::unordered_map<const ProofNode*, bool> cfaMap;
  std::unordered_set<Node> cfaAllowed;
  cfaAllowed.insert(fa.begin(), fa.end());
  std::shared_ptr<ProofNode> pft = pf;
  while (pft->getRule() == ProofRule::SCOPE)
  {
    const std::vector<Node>& args = pft->getArguments();
    cfaAllowed.insert(args.begin(), args.end());
    pft = pft->getChildren()[0];
  }
  Trace("pf-process") << "ProofNodeUpdater::process" << std::endl;
  std::unordered_map<std::shared_ptr<ProofNode>, bool> visited;
  std::unordered_map<std::shared_ptr<ProofNode>, bool>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  std::shared_ptr<ProofNode> cur;
  visit.push_back(pf);
  std::map<Node, std::shared_ptr<ProofNode>>::iterator itc;
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      // Check if there is a proof in resCache with the same result.
      // Note that if this returns true, we update the contents of the current
      // proof. Moreover, parents will replace the reference to this proof.
      // Thus, replacing the contents of this proof is not (typically)
      // necessary, but is done anyways in case there are any other references
      // to this proof that are not handled by this loop, that is, proof
      // nodes having this as a child that are not subproofs of pf.
      if (checkMergeProof(cur, resCache, cfaMap))
      {
        Trace("pf-process-merge") << "...merged on previsit" << std::endl;
        visited[cur] = true;
        continue;
      }
      preSimplify(cur);
      // run update to a fixed point
      bool continueUpdate = true;
      while (runUpdate(cur, fa, continueUpdate) && continueUpdate)
      {
        Trace("pf-process-debug") << "...updated proof." << std::endl;
      }
      visited[cur] = !continueUpdate;
      if (!continueUpdate)
      {
        // no further changes should be made to cur according to the callback
        Trace("pf-process-debug")
            << "...marked to not continue update." << std::endl;
        runFinalize(cur, fa, resCache, resCacheNcWaiting, cfaMap, cfaAllowed);
        continue;
      }
      traversing.push_back(cur);
      visit.push_back(cur);
      // If we are not the top-level proof, we were a scope, or became a scope
      // after updating, we do a separate recursive call to this method. This
      // allows us to properly track the assumptions in scope, which is
      // important for example to merge or to determine updates based on free
      // assumptions.
      if (cur->getRule() == ProofRule::SCOPE)
      {
        const std::vector<Node>& args = cur->getArguments();
        fa.insert(fa.end(), args.begin(), args.end());
      }
      const std::vector<std::shared_ptr<ProofNode>>& ccp = cur->getChildren();
      // now, process children
      for (const std::shared_ptr<ProofNode>& cp : ccp)
      {
        if (std::find(traversing.begin(), traversing.end(), cp)
            != traversing.end())
        {
          Unhandled()
              << "ProofNodeUpdater::processInternal: cyclic proof! (use "
                 "--proof-check=eager)"
              << std::endl;
        }
        visit.push_back(cp);
      }
    }
    else if (!it->second)
    {
      Assert(!traversing.empty());
      traversing.pop_back();
      visited[cur] = true;
      // finalize the node
      ProofRule id = cur->getRule();
      if (id == ProofRule::SCOPE)
      {
        const std::vector<Node>& args = cur->getArguments();
        Assert(fa.size() >= args.size());
        fa.resize(fa.size() - args.size());
      }
      // maybe found a proof in the meantime, i.e. a subproof of the current
      // proof with the same result. Same as above, updating the contents here
      // is typically not necessary since references to this proof will be
      // replaced.
      // maybe found a proof in the meantime, i.e. a subproof of the current
      // proof with the same result. Same as above, updating the contents here
      // is typically not necessary since references to this proof will be
      // replaced.
      if (!checkMergeProof(cur, resCache, cfaMap))
      {
        runFinalize(cur, fa, resCache, resCacheNcWaiting, cfaMap, cfaAllowed);
      }
      else
      {
        Trace("pf-process-merge") << "...merged on postvisit " << id << " / "
                                  << cur->getRule() << std::endl;
      }
      // call the finalize callback, independent of whether it was merged
      d_cb.finalize(cur);
    }
  } while (!visit.empty());
  Trace("pf-process") << "ProofNodeUpdater::process: finished" << std::endl;
}

void ProofNodeUpdater::preSimplify(std::shared_ptr<ProofNode> cur)
{
  if (!d_mergeSubproofs)
  {
    return;
  }
  std::shared_ptr<ProofNode> toMerge;
  do
  {
    ProofRule id = cur->getRule();
    toMerge = nullptr;
    switch (id)
    {
      case ProofRule::AND_ELIM:
      {
        // hardcoded for pattern (AND_ELIM (AND_INTRO ...))
        const std::vector<std::shared_ptr<ProofNode>>& children =
            cur->getChildren();
        Assert(children.size() == 1);
        if (children[0]->getRule() == ProofRule::AND_INTRO)
        {
          const std::vector<Node>& args = cur->getArguments();
          Assert(args.size() == 1);
          uint32_t i;
          if (ProofRuleChecker::getUInt32(args[0], i))
          {
            const std::vector<std::shared_ptr<ProofNode>>& cc =
                children[0]->getChildren();
            if (i < cc.size())
            {
              Trace("pfu-pre-simplify")
                  << "Pre-simplify AND_ELIM over AND_INTRO" << std::endl;
              toMerge = cc[i];
            }
          }
        }
      }
      break;
      case ProofRule::SYMM:
      {
        // hardcoded for pattern (SYMM (SYMM ...))
        const std::vector<std::shared_ptr<ProofNode>>& children =
            cur->getChildren();
        Assert(children.size() == 1);
        if (children[0]->getRule() == ProofRule::SYMM)
        {
          const std::vector<std::shared_ptr<ProofNode>>& cc =
              children[0]->getChildren();
          Trace("pfu-pre-simplify")
              << "Pre-simplify SYMM over SYMM" << std::endl;
          toMerge = cc[0];
        }
      }
      break;
      default: break;
    }
    // Generic search, which checks if there is a descendent of this proof node
    // (up to a default bound, set to 2), which proves the same conclusion as
    // this node. If this is the case, then we immediately take that subproof.
    // This heuristic makes a big difference for proofs e.g. of the form
    // F1 ......... Fn
    // ---------------- AND_INTRO
    // (and F1 .... Fn)
    // ---------------- MACRO_SR_PRED_INTRO
    // false
    // where one of Fi is false. In this case, we *only* want to post-process
    // the proof of Fi.
    // The case above occurs often in practice when a single assertion in the
    // rewrite rewrites to false. This optimization saves the internal work of
    // post-processing F1 ... F{i-1} F{i+1} ... Fn. The depth is configurable by
    // --proof-pre-simp-lookahead=N, default 2.
    uint64_t depthLimit = options().proof.proofPreSimpLookahead;
    if (toMerge == nullptr && depthLimit > 0)
    {
      Node res = cur->getResult();
      std::vector<std::pair<size_t, std::shared_ptr<ProofNode>>> toProcess;
      toProcess.emplace_back(0, cur);
      std::unordered_map<std::shared_ptr<ProofNode>, size_t> processed;
      std::unordered_map<std::shared_ptr<ProofNode>, size_t>::iterator itp;
      do
      {
        std::pair<size_t, std::shared_ptr<ProofNode>> p = toProcess.back();
        toProcess.pop_back();
        std::shared_ptr<ProofNode> cc = p.second;
        // do not traverse SCOPE
        if (cc->getRule() == ProofRule::SCOPE)
        {
          continue;
        }
        itp = processed.find(cc);
        if (itp != processed.end() && p.first >= itp->second)
        {
          continue;
        }
        if (p.first > 0)
        {
          if (cc->getResult() == res)
          {
            toMerge = cc;
            break;
          }
        }
        if (p.first < depthLimit)
        {
          const std::vector<std::shared_ptr<ProofNode>>& children =
              cc->getChildren();
          for (const std::shared_ptr<ProofNode>& cp : children)
          {
            toProcess.emplace_back(p.first + 1, cp);
          }
        }
      } while (!toProcess.empty());
    }
    if (toMerge != nullptr && toMerge != cur)
    {
      ProofNodeManager* pnm = d_env.getProofNodeManager();
      pnm->updateNode(cur.get(), toMerge.get());
    }
  } while (toMerge != nullptr);
}

bool ProofNodeUpdater::updateProofNode(std::shared_ptr<ProofNode> cur,
                                       const std::vector<Node>& fa,
                                       bool& continueUpdate,
                                       bool preVisit)
{
  ProofRule id = cur->getRule();
  // use CDProof to open a scope for which the callback updates
  CDProof cpf(d_env, nullptr, "ProofNodeUpdater::CDProof", d_autoSym);
  const std::vector<std::shared_ptr<ProofNode>>& cc = cur->getChildren();
  std::vector<Node> ccn;
  for (const std::shared_ptr<ProofNode>& cp : cc)
  {
    Node cpres = cp->getResult();
    ccn.push_back(cpres);
    // store in the proof
    cpf.addProof(cp);
  }
  Node res = cur->getResult();
  Trace("pf-process-debug")
      << "Updating (" << cur->getRule() << "): " << res << std::endl;
  // only if the callback updated the node
  if (preVisit
          ? d_cb.update(res, id, ccn, cur->getArguments(), &cpf, continueUpdate)
          : d_cb.updatePost(res, id, ccn, cur->getArguments(), &cpf))
  {
    std::shared_ptr<ProofNode> npn = cpf.getProofFor(res);
    std::vector<Node> fullFa;
    if (d_debugFreeAssumps)
    {
      expr::getFreeAssumptions(cur.get(), fullFa);
      Trace("pfnu-debug") << "Original proof : " << *cur << std::endl;
    }
    // then, update the original proof node based on this one
    Trace("pf-process-debug") << "Update node..." << std::endl;
    d_env.getProofNodeManager()->updateNode(cur.get(), npn.get());
    Trace("pf-process-debug") << "...update node finished." << std::endl;
    if (d_debugFreeAssumps)
    {
      fullFa.insert(fullFa.end(), fa.begin(), fa.end());
      // We have that npn is a node we occurring the final updated version of
      // the proof. We can now debug based on the expected set of free
      // assumptions.
      Trace("pfnu-debug") << "Ensure updated closed..." << std::endl;
      pfnEnsureClosedWrt(options(),
                         npn.get(),
                         fullFa,
                         "pfnu-debug",
                         "ProofNodeUpdater:postupdate");
    }
    // since we updated, we pre-simplify again
    preSimplify(cur);
    Trace("pf-process-debug") << "..finished" << std::endl;
    return true;
  }
  Trace("pf-process-debug") << "..finished" << std::endl;
  return false;
}

bool ProofNodeUpdater::runUpdate(std::shared_ptr<ProofNode> cur,
                                 const std::vector<Node>& fa,
                                 bool& continueUpdate,
                                 bool preVisit)
{
  // should it be updated?
  if (preVisit ? !d_cb.shouldUpdate(cur, fa, continueUpdate)
               : !d_cb.shouldUpdatePost(cur, fa))
  {
    return false;
  }
  return updateProofNode(cur, fa, continueUpdate, preVisit);
}

void ProofNodeUpdater::runFinalize(
    std::shared_ptr<ProofNode> cur,
    const std::vector<Node>& fa,
    std::map<Node, std::shared_ptr<ProofNode>>& resCache,
    std::map<Node, std::vector<std::shared_ptr<ProofNode>>>& resCacheNcWaiting,
    std::unordered_map<const ProofNode*, bool>& cfaMap,
    const std::unordered_set<Node>& cfaAllowed)
{
  // run update (marked as post-visit) to a fixed point
  bool dummyContinueUpdate;
  while (runUpdate(cur, fa, dummyContinueUpdate, false))
  {
    Trace("pf-process-debug") << "...updated proof." << std::endl;
  }
  if (d_mergeSubproofs)
  {
    Node res = cur->getResult();
    // cache the result if we don't contain an assumption
    if (!expr::containsAssumption(cur.get(), cfaMap, cfaAllowed))
    {
      Trace("pf-process-debug") << "No assumption pf: " << res << std::endl;
      // cache result if we are merging subproofs
      resCache[res] = cur;
      // go back and merge into the non-closed proofs of the same fact
      std::map<Node, std::vector<std::shared_ptr<ProofNode>>>::iterator itnw =
          resCacheNcWaiting.find(res);
      if (itnw != resCacheNcWaiting.end())
      {
        ProofNodeManager* pnm = d_env.getProofNodeManager();
        for (std::shared_ptr<ProofNode>& ncp : itnw->second)
        {
          pnm->updateNode(ncp.get(), cur.get());
        }
        resCacheNcWaiting.erase(res);
      }
    }
    else
    {
      Trace("pf-process-debug") << "Assumption pf: " << res << ", with "
                                << cfaAllowed.size() << std::endl;
      resCacheNcWaiting[res].push_back(cur);
    }
    // Now, do update of children, that is, we replace children of the current
    // proof with the representative child in the cache, if they are different.
    // This is necessary to do here since we only locally update the contents of
    // a proof when a duplicate is encountered. Updating the reference to a
    // child is done here.
    std::map<Node, std::shared_ptr<ProofNode>>::iterator itr;
    const std::vector<std::shared_ptr<ProofNode>>& ccp = cur->getChildren();
    std::vector<std::shared_ptr<ProofNode>> newChildren;
    bool childChanged = false;
    for (const std::shared_ptr<ProofNode>& cp : ccp)
    {
      Node cpres = cp->getResult();
      itr = resCache.find(cpres);
      if (itr != resCache.end() && itr->second != cp)
      {
        newChildren.emplace_back(itr->second);
        childChanged = true;
      }
      else
      {
        newChildren.emplace_back(cp);
      }
    }
    if (childChanged)
    {
      ProofNodeManager* pnm = d_env.getProofNodeManager();
      pnm->updateNode(
          cur.get(), cur->getRule(), newChildren, cur->getArguments());
    }
  }
  if (d_debugFreeAssumps)
  {
    // We have that npn is a node we occurring the final updated version of
    // the proof. We can now debug based on the expected set of free
    // assumptions.
    Trace("pfnu-debug") << "Ensure update closed..." << std::endl;
    pfnEnsureClosedWrt(
        options(), cur.get(), fa, "pfnu-debug", "ProofNodeUpdater:finalize");
  }
}

bool ProofNodeUpdater::checkMergeProof(
    std::shared_ptr<ProofNode>& cur,
    const std::map<Node, std::shared_ptr<ProofNode>>& resCache,
    std::unordered_map<const ProofNode*, bool>& cfaMap)
{
  if (d_mergeSubproofs)
  {
    const Node& res = cur->getResult();
    std::map<Node, std::shared_ptr<ProofNode>>::const_iterator itc =
        resCache.find(res);
    if (itc != resCache.end())
    {
      ProofNodeManager* pnm = d_env.getProofNodeManager();
      Assert(pnm != nullptr);
      // already have a proof, merge it into this one
      pnm->updateNode(cur.get(), itc->second.get());
      // does not contain free assumptions since the range of resCache does
      // not contain free assumptions
      cfaMap[cur.get()] = false;
      return true;
    }
  }
  return false;
}

void ProofNodeUpdater::setFreeAssumptions(const std::vector<Node>& freeAssumps,
                                          bool doDebug)
{
  d_freeAssumps.clear();
  d_freeAssumps.insert(
      d_freeAssumps.end(), freeAssumps.begin(), freeAssumps.end());
  d_debugFreeAssumps = doDebug;
}

}  // namespace cvc5::internal
