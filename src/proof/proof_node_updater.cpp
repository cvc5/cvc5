/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Hanna Lachnitt
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of a utility for updating proof nodes.
 */

#include "proof/proof_node_updater.h"

#include "proof/lazy_proof.h"
#include "proof/proof_ensure_closed.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"

namespace cvc5::internal {

ProofNodeUpdaterCallback::ProofNodeUpdaterCallback() {}
ProofNodeUpdaterCallback::~ProofNodeUpdaterCallback() {}

bool ProofNodeUpdaterCallback::update(Node res,
                                      PfRule id,
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
                                          PfRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args,
                                          CDProof* cdp)
{
  return false;
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
  Trace("pf-process") << "ProofNodeUpdater::process" << std::endl;
  std::unordered_map<std::shared_ptr<ProofNode>, bool> visited;
  std::unordered_map<std::shared_ptr<ProofNode>, bool>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  std::shared_ptr<ProofNode> cur;
  visit.push_back(pf);
  std::map<Node, std::shared_ptr<ProofNode>>::iterator itc;
  Node res;
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  Assert(pnm != nullptr);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    res = cur->getResult();
    if (it == visited.end())
    {
      if (d_mergeSubproofs)
      {
        itc = resCache.find(res);
        if (itc != resCache.end())
        {
          // already have a proof, merge it into this one
          visited[cur] = true;
          pnm->updateNode(cur.get(), itc->second.get());
          // does not contain free assumptions since the range of resCache does
          // not contain free assumptions
          cfaMap[cur.get()] = false;
          continue;
        }
      }
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
        runFinalize(cur, fa, resCache, resCacheNcWaiting, cfaMap);
        continue;
      }
      traversing.push_back(cur);
      visit.push_back(cur);
      // If we are not the top-level proof, we were a scope, or became a scope
      // after updating, we do a separate recursive call to this method. This
      // allows us to properly track the assumptions in scope, which is
      // important for example to merge or to determine updates based on free
      // assumptions.
      if (cur->getRule() == PfRule::SCOPE)
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
      if (cur->getRule() == PfRule::SCOPE)
      {
        const std::vector<Node>& args = cur->getArguments();
        Assert(fa.size() >= args.size());
        fa.resize(fa.size() - args.size());
      }
      runFinalize(cur, fa, resCache, resCacheNcWaiting, cfaMap);
    }
  } while (!visit.empty());
  Trace("pf-process") << "ProofNodeUpdater::process: finished" << std::endl;
}

bool ProofNodeUpdater::updateProofNode(std::shared_ptr<ProofNode> cur,
                                       const std::vector<Node>& fa,
                                       bool& continueUpdate,
                                       bool preVisit)
{
  PfRule id = cur->getRule();
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
    std::unordered_map<const ProofNode*, bool>& cfaMap)
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
    if (!expr::containsAssumption(cur.get(), cfaMap))
    {
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
      resCacheNcWaiting[res].push_back(cur);
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

void ProofNodeUpdater::setDebugFreeAssumptions(
    const std::vector<Node>& freeAssumps)
{
  d_freeAssumps.clear();
  d_freeAssumps.insert(
      d_freeAssumps.end(), freeAssumps.begin(), freeAssumps.end());
  d_debugFreeAssumps = true;
}

}  // namespace cvc5::internal
