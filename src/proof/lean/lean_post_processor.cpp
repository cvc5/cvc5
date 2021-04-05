/*********************                                                        */
/*! \file lean_post_processor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the Lean post processor
 **/

#include "proof/lean/lean_post_processor.h"

#include "expr/lazy_proof.h"
#include "expr/proof_checker.h"
#include "expr/proof_node_algorithm.h"
#include "expr/proof_node_manager.h"
#include "proof/lean/lean_rules.h"

namespace cvc5 {

namespace proof {

LeanProofPostprocessCallback::LeanProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm), d_pc(pnm->getChecker())
{
}

LeanProofPostprocess::LeanProofPostprocess(ProofNodeManager* pnm)
    : d_cb(new proof::LeanProofPostprocessCallback(pnm)), d_pnm(pnm)
{
}

bool LeanProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                const std::vector<Node>& fa,
                                                bool& continueUpdate)
{
  return pn->getRule() != PfRule::LEAN_RULE;
};

bool LeanProofPostprocessCallback::addLeanStep(
    Node res,
    LeanRule rule,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  NodeManager* nm = NodeManager::currentNM();
  Node leanId = nm->mkConst<Rational>(static_cast<unsigned>(rule));
  std::vector<Node> leanArgs = {leanId, res};
  leanArgs.insert(leanArgs.end(), args.begin(), args.end());
  return cdp.addStep(res, PfRule::LEAN_RULE, children, leanArgs);
}

bool LeanProofPostprocessCallback::update(Node res,
                                          PfRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args,
                                          CDProof* cdp,
                                          bool& continueUpdate)
{
  switch (id)
  {
    case PfRule::ASSUME:
    {
      return addLeanStep(res, LeanRule::ASSUME, children, args, *cdp);
    }
    case PfRule::SCOPE:
    {
      return addLeanStep(res, LeanRule::SCOPE, children, args, *cdp);
    }
    case PfRule::CHAIN_RESOLUTION:
    {
      Node cur = children[0];
      for (size_t i = 1, size = children.size(); i < size; i++)
      {
        std::vector<Node> newChildren{cur, children[i]};
        std::vector<Node> newArgs{args[(i - 1) * 2], args[(i - 1) * 2 + 1]};
        cur = d_pc->checkDebug(
            PfRule::RESOLUTION, newChildren, newArgs, Node(), "");
        addLeanStep(cur,
                    newArgs[0].getConst<bool>() ? LeanRule::R1 : LeanRule::R0,
                    newChildren,
                    {newArgs[1]},
                    *cdp);
      }
      break;
    }
    case PfRule::REFL:
    {
      return addLeanStep(res, LeanRule::SMTREFL, {}, {}, *cdp);
    }
    case PfRule::SYMM:
    {
      addLeanStep(res,
                  res.getKind() == kind::EQUAL ? LeanRule::SMTSYMM
                                               : LeanRule::SMTSYMM_NEG,
                  {},
                  {},
                  *cdp);
      break;
    }
    default: { return false;
    }
  };
  return true;
}

void LeanProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  ProofNodeUpdater updater(d_pnm, *(d_cb.get()));
  updater.process(pf);
};

}  // namespace proof
}  // namespace cvc5
