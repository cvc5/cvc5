/*********************                                                        */
/*! \file lfsc_post_processor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the Lfsc post proccessor
 **/

#include "proof/lfsc/lfsc_post_processor.h"
#include "proof/lfsc/lfsc_printer.h"

#include "expr/lazy_proof.h"
#include "expr/proof_checker.h"
#include "expr/proof_node_algorithm.h"
#include "expr/proof_node_updater.h"

namespace CVC4 {
namespace proof {

LfscProofPostprocessCallback::LfscProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm), d_pc(pnm->getChecker()), d_lcb(), d_tproc(&d_lcb)
{
}

LfscProofPostprocess::LfscProofPostprocess(ProofNodeManager* pnm)
    : d_cb(new proof::LfscProofPostprocessCallback(pnm)), d_pnm(pnm)
{
}

bool LfscProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                bool& continueUpdate)
{
  return pn->getRule() != PfRule::LFSC_RULE;
}

bool LfscProofPostprocessCallback::update(Node res,
                                          PfRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args,
                                          CDProof* cdp,
                                          bool& continueUpdate)
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(id != PfRule::LFSC_RULE);

  // convert children to internal form
  std::vector<Node> ics;
  for (const Node& c : children)
  {
    ics.push_back(d_tproc.toInternal(c));
  }

  // convert arguments to internal form
  std::vector<Node> ias;
  for (const Node& a : args)
  {
    ias.push_back(d_tproc.toInternal(a));
  }

  switch (id)
  {
    case PfRule::CHAIN_RESOLUTION:
    {
      Node cur = children[0];
      for (size_t i = 1, size = children.size(); i < size; i++)
      {
        std::vector<Node> newChildren{cur, children[i]};

     std::vector<Node> newArgs{args[(i - 1) * 2], args[(i - 1) * 2 + 1]};
        cur = d_pc->checkDebug(
            PfRule::RESOLUTION, newChildren, newArgs, Node(), "");
        cdp->addStep(cur, PfRule::RESOLUTION, newChildren, newArgs);
      }
    }
    break;
    case PfRule::TRANS:
    {
      // nested
    }
    break;
    case PfRule::CONG:
    {
      // nested
    }
    break;
    case PfRule::AND_ELIM:
    {
      uint32_t i;
      bool b = ProofRuleChecker::getUInt32(args[0], i);
      Assert(b);
      //      Node cur = ics[0];
      Node cur = children[0];
      for (uint32_t j = 0; j < i; j++)
      {
        // Assert(cur.getKind() == kind::AND);
        // Assert(cur.getNumChildren() == 2);
        //        Node cur_r = cur[1];
        std::vector<Node> r_children(cur.begin() + 1, cur.end());
        Node cur_r = nm->mkAnd(r_children);
        cdp->addStep(cur_r,
                     PfRule::LFSC_RULE,
                     {cur},
                     {mkLfscRuleNode(LfscRule::CNF_AND_POS_2), cur_r});
        cur = cur_r;
      }
      if (i != children[0].getNumChildren() - 1)
      {
        cdp->addStep(cur[0],
                     PfRule::LFSC_RULE,
                     {cur},
                     {mkLfscRuleNode(LfscRule::CNF_AND_POS_1), cur[0]});
      }
    }
    break;
    default: return false; break;
  }
  return true;
}

void LfscProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  ProofNodeUpdater updater(d_pnm, *(d_cb.get()));
  updater.process(pf);
}

}  // namespace proof
}  // namespace CVC4
