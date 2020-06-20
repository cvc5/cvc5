/*********************                                                        */
/*! \file proof_post_processor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of module for processing proof nodes
 **/

#include "smt/proof_post_processor.h"

#include "expr/lazy_proof.h"
#include "theory/eager_proof_generator.h"

using namespace CVC4::theory;
using namespace CVC4::kind;

namespace CVC4 {
namespace smt {

ProofPostProcessor::ProofPostProcessor(ProofNodeManager * pnm) : d_pnm(pnm)
{
  // always eliminate macro rules (add to d_elimRules?)
}

void ProofPostProcessor::eliminate(PfRule rule)
{
  d_elimRules.insert(rule);
}

void ProofPostProcessor::process(std::shared_ptr<ProofNode> pf)
{
  Trace("pf-process") << "ProofPostProcessor::process" << std::endl;
  ProofChecker * pc = d_pnm->getChecker();
  std::unordered_set<ProofNode*> visited;
  std::unordered_set<ProofNode*>::iterator it;
  std::vector<ProofNode*> visit;
  ProofNode* cur;
  visit.push_back(pf.get());
  do
  {
    cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited.insert(cur);
      // should it be eliminated?
      PfRule id = cur->getRule();
      if (d_elimRules.find(id)!=d_elimRules.end())
      {
        // process using checker?
        ProofRuleChecker * prc = pc->getCheckerFor(id);
        if (prc!=nullptr)
        {
          EagerProofGenerator epg(d_pnm);
          const std::vector<std::shared_ptr<ProofNode>>& cc = cur->getChildren();
          std::vector<Node> ccn;
          for (const std::shared_ptr<ProofNode>& cp : cc)
          {
            Node cpres = cp->getResult();
            ccn.push_back(cpres);
            // store in the eager proof generator
            epg.setProofFor(cpres, cp);
          }
          LazyCDProof lcp(d_pnm, &epg);
          // only if expand
          if (prc->expand(id,ccn,cur->getArguments(),&lcp))
          {
            // build the proof, which should be closed
            std::shared_ptr<ProofNode> npn = lcp.getProofFor(cur->getResult());
            Assert (npn->isClosed());
            // then, update the original proof node based on this one
            d_pnm->updateNode(cur, npn.get());
          }
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
  Trace("pf-process") << "ProofPostProcessor::process: finished" << std::endl;
}

}  // namespace smt
}  // namespace CVC4
