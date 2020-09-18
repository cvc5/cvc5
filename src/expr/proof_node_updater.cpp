/*********************                                                        */
/*! \file proof_node_updater.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of a utility for updating proof nodes
 **/

#include "expr/proof_node_updater.h"

#include "expr/lazy_proof.h"
#include "expr/proof_node_algorithm.h"

namespace CVC4 {

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

ProofNodeUpdater::ProofNodeUpdater(ProofNodeManager* pnm,
                                   ProofNodeUpdaterCallback& cb)
    : d_pnm(pnm), d_cb(cb), d_debugFreeAssumps(false)
{
}

void ProofNodeUpdater::process(std::shared_ptr<ProofNode> pf)
{
  if (d_debugFreeAssumps)
  {
    if (Trace.isOn("pfnu-debug"))
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
                                       const std::vector<Node>& fa)
{
  Trace("pf-process") << "ProofNodeUpdater::process" << std::endl;
  std::unordered_map<std::shared_ptr<ProofNode>, bool> visited;
  std::unordered_map<std::shared_ptr<ProofNode>, bool>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  std::shared_ptr<ProofNode> cur;
  visit.push_back(pf);
  std::map<Node, std::shared_ptr<ProofNode>>::iterator itc;
  // A cache from formulas to proof nodes that are in the current scope.
  // Notice that we make a fresh recursive call to process if the current
  // rule is SCOPE below.
  std::map<Node, std::shared_ptr<ProofNode>> resCache;
  Node res;
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    res = cur->getResult();
    if (it == visited.end())
    {
      itc = resCache.find(res);
      if (itc != resCache.end())
      {
        // already have a proof
        visited[cur] = true;
        d_pnm->updateNode(cur.get(), itc->second.get());
      }
      else
      {
        visited[cur] = false;
        // run update to a fixed point
        bool continueUpdate = true;
        while (runUpdate(cur, fa, continueUpdate) && continueUpdate)
        {
          Trace("pf-process-debug") << "...updated proof." << std::endl;
        }
        if (!continueUpdate)
        {
          // no further changes should be made to cur according to the callback
          Trace("pf-process-debug")
              << "...marked to not continue update." << std::endl;
          continue;
        }
        visit.push_back(cur);
        // If we are not the top-level proof, we were a scope, or became a
        // scope after updating, we need to make a separate recursive call to
        // this method.
        if (cur->getRule() == PfRule::SCOPE && cur != pf)
        {
          std::vector<Node> nfa;
          // if we are debugging free assumptions, update the set
          if (d_debugFreeAssumps)
          {
            nfa.insert(nfa.end(), fa.begin(), fa.end());
            const std::vector<Node>& args = cur->getArguments();
            nfa.insert(nfa.end(), args.begin(), args.end());
            Trace("pfnu-debug2")
                << "Process new scope with " << args << std::endl;
          }
          // Process in new call separately, since we should not cache
          // the results of proofs that have a different scope.
          processInternal(cur, nfa);
          continue;
        }
        const std::vector<std::shared_ptr<ProofNode>>& ccp = cur->getChildren();
        // now, process children
        for (const std::shared_ptr<ProofNode>& cp : ccp)
        {
          visit.push_back(cp);
        }
      }
    }
    else if (!it->second)
    {
      visited[cur] = true;
      // cache result
      resCache[res] = cur;
      if (d_debugFreeAssumps)
      {
        // We have that npn is a node we occurring the final updated version of
        // the proof. We can now debug based on the expected set of free
        // assumptions.
        Trace("pfnu-debug") << "Ensure update closed..." << std::endl;
        pfnEnsureClosedWrt(
            cur.get(), fa, "pfnu-debug", "ProofNodeUpdater:finalize");
      }
    }
  } while (!visit.empty());
  Trace("pf-process") << "ProofNodeUpdater::process: finished" << std::endl;
}

bool ProofNodeUpdater::runUpdate(std::shared_ptr<ProofNode> cur,
                                 const std::vector<Node>& fa,
                                 bool& continueUpdate)
{
  // should it be updated?
  if (!d_cb.shouldUpdate(cur.get()))
  {
    return false;
  }
  PfRule id = cur->getRule();
  // use CDProof to open a scope for which the callback updates
  CDProof cpf(d_pnm);
  const std::vector<std::shared_ptr<ProofNode>>& cc = cur->getChildren();
  std::vector<Node> ccn;
  for (const std::shared_ptr<ProofNode>& cp : cc)
  {
    Node cpres = cp->getResult();
    ccn.push_back(cpres);
    // store in the proof
    cpf.addProof(cp);
  }
  Trace("pf-process-debug")
      << "Updating (" << cur->getRule() << ")..." << std::endl;
  Node res = cur->getResult();
  // only if the callback updated the node
  if (d_cb.update(res, id, ccn, cur->getArguments(), &cpf, continueUpdate))
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
    d_pnm->updateNode(cur.get(), npn.get());
    Trace("pf-process-debug") << "...update node finished." << std::endl;
    if (d_debugFreeAssumps)
    {
      fullFa.insert(fullFa.end(), fa.begin(), fa.end());
      // We have that npn is a node we occurring the final updated version of
      // the proof. We can now debug based on the expected set of free
      // assumptions.
      Trace("pfnu-debug") << "Ensure update closed..." << std::endl;
      pfnEnsureClosedWrt(
          npn.get(), fullFa, "pfnu-debug", "ProofNodeUpdater:postupdate");
    }
    Trace("pf-process-debug") << "..finished" << std::endl;
    return true;
  }
  Trace("pf-process-debug") << "..finished" << std::endl;
  return false;
}

void ProofNodeUpdater::setDebugFreeAssumptions(
    const std::vector<Node>& freeAssumps)
{
  d_freeAssumps.clear();
  d_freeAssumps.insert(
      d_freeAssumps.end(), freeAssumps.begin(), freeAssumps.end());
  d_debugFreeAssumps = true;
}

}  // namespace CVC4
