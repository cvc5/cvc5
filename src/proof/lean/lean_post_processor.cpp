/*********************                                                        */
/*! \file lean_post_processor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the Lean post proccessor
 **/

#include "proof/lean/lean_post_processor.h"

#include "../../expr/proof_node_updater.h"
#include "expr/lazy_proof.h"
#include "expr/proof_checker.h"
#include "expr/proof_node_algorithm.h"
#include "proof/lean/lean_rules.h"

namespace CVC4 {

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
                                                bool& continueUpdate)
{
  return (pn->getRule() != PfRule::LEAN_RULE);
};

bool LeanProofPostProcessCallback::addLeanStep(
    Node res,
    LeanRule rule,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  Node lean_id = nm->mkConst<Rational>(static_cast<unsigned>(rule));
  std::vector<Node> lean_args = {lean_id, res};
  lean_args.insert(lean_args.end(), args.begin(), args.end());
  return cdp->addStep(res, PfRule::LEAN_RULE, children, lean_args);
}
bool LeanProofPostprocessCallback::update(Node res,
                                          PfRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args,
                                          CDProof* cdp,
                                          bool& continueUpdate)
{
  NodeManager* nm = NodeManager::currentNM();
  // change to case
  // Trace("Hello") << id << "\n";
  switch (id)
  {
    case PfRule::ASSUME:
    {
      return addLeanStep(res, LeanRule::ASSUME, children, {}, *cdp);
    }
    case PfRule::SCOPE:
    {  // not sure here
      return addLeanStep(res, LeanRule::SCOPE, children, {}, *cdp);
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
        if (newArgs[0].getConst<bool>())
        {
          bool _ = addLeanStep(cur, LeanRule::R1, newChildren, {newArgs[1]}, *cdp);
        }
        else
        {
          bool _ = addLeanStep(cur, LeanRule::R0, newChildren, {newArgs[1]}, *cdp);
        }
      }
      break;
    }
    case PfRule::REFL:
    {
      return addLeanStep(res, LeanRule::SMTREFL, children, {}, *cdp);
    }
    case PfRule::MACRO_RESOLUTION:
    {
      return addLeanStep(res, LeanRule::TRUST, children, {}, *cdp);
    }

    /*
    case PfRule::RESOLUTION:
    {
      Node lean_id = nm->mkConst<Rational>(static_cast<unsigned>(
          args[0] == nm->mkConst(true) ? proof::LeanRule::R0
                                       : proof::LeanRule::R1));
      std::vector<Node> lean_args;
      lean_args.push_back(lean_id);
      lean_args.insert(lean_args.end(), args.begin(), args.end());
      cdp->addStep(res, PfRule::LEAN_RULE, children, lean_args);
      break;
    }
    case PfRule::SYMM:
    {
      Node child = children[0];
      Kind k = child.getKind();
      Node new_id, t1, t2, c1, c2, new_res;
      if (k == kind::EQUAL)
      {
        new_id = nm->mkConst<Rational>(
            static_cast<unsigned>(proof::LeanRule::SMTSYMM));
        t1 = child[0];
        t2 = child[1];
        c1 = nm->mkNode(kind::NOT, nm->mkNode(kind::EQUAL, t1, t2));
        c2 = nm->mkNode(kind::EQUAL, t2, t1);
        new_res = nm->mkNode(c1, c2);
      }
      else
      {
        new_id = nm->mkConst<Rational>(
            static_cast<unsigned>(proof::LeanRule::SMTSYMM_NEG));
        t1 = child[0][0];
        t2 = child[0][1];
        c1 = nm->mkNode(kind::EQUAL, t1, t2);
        c2 = nm->mkNode(kind::NOT, nm->mkNode(kind::EQUAL, t2, t1));
        new_res = nm->mkNode(c1, c2);
      }
      std::vector<Node> new_args = {new_id, t1, t2};
      cdp->addStep(new_res, PfRule::LEAN_RULE, {}, new_args);
      break;
    }
    case PfRule::TRANS:
    {
      Node new_id = nm->mkConst<Rational>(
          static_cast<unsigned>(proof::LeanRule::SMTTRANSN));
      Node t1, t2, ineq, new_res;
      std::vector<Node> clauses;
      for (Node child : children)
      {
        t1 = child[0][0];
        t2 = child[0][1];
        ineq = nm->mkNode(kind::NOT, nm->mkNode(kind::EQUAL, t1, t2));
        clauses.push_back(ineq);
      }
      clauses.push_back(nm->mkNode(
          kind::EQUAL, children.front()[0][0], children.back()[0][1]));
      cdp->addStep(res, PfRule::LEAN_RULE, children, args);
      break;
    }
    case (PfRule::CONG):
    {
      Node new_id =
          nm->mkConst<Rational>(static_cast<unsigned>(proof::LeanRule::CONGN));
      // congn -- lean takes term and two clauses
      // results in a list of ineqs, than an eq
      std::vector<Node> conclusion_nodes;
      for (Node n : children)
      {
        Node ineq = nm->mkNode(kind::NOT, nm->mkNode(kind::EQUAL, n[0], n[1]));
        conclusion_nodes.push_back(ineq);
      }
      Node eq_node = nm->mkNode(kind::EQUAL, children.front()[0],
    children.back()[1]); conclusion_nodes.push_back(eq_node); Node new_res =
    nm->mkNode(conclusion_nodes);
      // args will be the function and clauses
      cdp->addStep(
          new_res, PfRule::LEAN_RULE, {}, args);  // take no children, only args
      break;
    }
    // chain reso, reordering, implies_elim, scope
    case (PfRule::IMPLIES_ELIM):
    {
      Node new_id = nm->mkConst<Rational>(
          static_cast<unsigned>(proof::LeanRule::CNF_IMPLIES));
      cdp->addStep(res, PfRule::LEAN_RULE, children, {new_id});  // add child
      break;
    }
    case (PfRule::REORDERING): { // not sure here
      Node new_id = nm->mkConst<Rational>(
          static_cast<unsigned>(proof::LeanRule::CNF_IMPLIES));
      cdp->addStep(res, PfRule::LEAN_RULE, children, {new_id});  // add child
      break;
    }
    */
    default:
    {
      // Trace("Hello") << res << "\n";
      return false;
    }
  };
  // Trace("Hello") << res << "\n";
  return true;
}  // namespace proof

void LeanProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  ProofNodeUpdater updater(d_pnm, *(d_cb.get()));
  updater.process(pf);
};

}  // namespace proof
}  // namespace CVC4
