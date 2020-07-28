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

namespace CVC4 {

ProofNodeUpdaterCallback::ProofNodeUpdaterCallback() {}
ProofNodeUpdaterCallback::~ProofNodeUpdaterCallback() {}

ProofNodeUpdater::ProofNodeUpdater(ProofNodeManager* pnm,
                                   ProofNodeUpdaterCallback& cb)
    : d_pnm(pnm), d_cb(cb)
{
}

void ProofNodeUpdater::process(std::shared_ptr<ProofNode> pf)
{
  Trace("pf-process") << "ProofNodeUpdater::process" << std::endl;
  std::unordered_set<ProofNode*> visited;
  std::unordered_set<ProofNode*>::iterator it;
  std::vector<ProofNode*> visit;
  ProofNode* cur;
  visit.push_back(pf.get());
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited.insert(cur);
      // should it be updated?
      if (d_cb.shouldUpdate(cur))
      {
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
        // only if the callback updated the node
        if (d_cb.update(id, ccn, cur->getArguments(), &cpf))
        {
          // build the proof, which should be closed
          std::shared_ptr<ProofNode> npn = cpf.getProofFor(cur->getResult());
          Assert(npn->isClosed());
          // then, update the original proof node based on this one
          d_pnm->updateNode(cur, npn.get());
        }
      }
      const std::vector<std::shared_ptr<ProofNode>>& ccp = cur->getChildren();
      // now, process children
      for (const std::shared_ptr<ProofNode>& cp : ccp)
      {
        visit.push_back(cp.get());
      }
    }
  } while (!visit.empty());
  Trace("pf-process") << "ProofNodeUpdater::process: finished" << std::endl;
}

}  // namespace CVC4
