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
#include "options/proof_options.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace proof {

LfscProofPostprocessCallback::LfscProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm), d_pc(pnm->getChecker())
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
    ics.push_back(d_tproc.convert(c));
  }

  // convert arguments to internal form
  std::vector<Node> ias;
  for (const Node& a : args)
  {
    ias.push_back(d_tproc.convert(a));
  }

  switch (id)
  {
    case PfRule::CHAIN_RESOLUTION:
    {
      // turn into binary resolution
      Node cur = children[0];
      for (size_t i = 1, size = children.size(); i < size; i++)
      {
        std::vector<Node> newChildren{cur, children[i]};
        std::vector<Node> newArgs{args[(i - 1) * 2], args[(i - 1) * 2 + 1]};
        cur = d_pc->checkDebug(
            PfRule::RESOLUTION, newChildren, newArgs);
        cdp->addStep(cur, PfRule::RESOLUTION, newChildren, newArgs);
      }
    }
    break;
    case PfRule::TRANS:
    {
      if (children.size()>2)
      {
        // turn into binary
        Node cur = children[0];
        for (size_t i = 1, size = children.size(); i < size; i++)
        {
          std::vector<Node> newChildren{cur, children[i]};
          cur = d_pc->checkDebug(
              PfRule::TRANS, newChildren, {});
          cdp->addStep(cur, PfRule::TRANS, newChildren, {});
        }
        return true;
      }
      return false;
    }
    break;
    case PfRule::CONG:
    {
      Assert (res.getKind()==EQUAL);
      // We are proving f(t1, ..., tn) = f(s1, ..., sn), nested.
      // The intermediate proofs prove:
      // f(t1, ..., tn) = f(t1, ..., tn)
      // f(t1, ..., tn) = f(s1, t2, ..., tn)
      // f(t1, ..., tn) = f(s1, s2, t3, ..., tn)
      // ...
      // f(t1, ..., tn) = f(s1, ..., sn)
      //Node cur = res[0].eqNode(res[0]);
      //cdp->addStep(cur, PfRule::REFL, {}
      for (size_t i = 1, size = children.size(); i < size; i++)
      {
      }
      // nested
      return false;
    }
    break;
    case PfRule::AND_ELIM:
    {
      uint32_t i;
      bool b = ProofRuleChecker::getUInt32(args[0], i);
      Assert(b);
      // we start with the n-ary AND
      Node cur = children[0];
      std::vector<Node> cchildren(cur.begin(), cur.end());
      // get its chain form
      Node curChain = mkChain(AND, cchildren);
      // currently there is assymmetry on how the first step below is handled,
      // where from n-ary AND we conclude a chained AND. This could be made
      // symmetric by an explicit, internal-only rule to conclude chained form
      // from n-ary form.
      for (uint32_t j = 0; j < i; j++)
      {
        Node cur_r = j == 0 ? curChain[1] : cur[1];
        addLfscRule(cdp, cur_r, {cur}, LfscRule::CNF_AND_POS_2, {});
        cur = cur_r;
      }
      // We always get the left child, even if we are at the end
      // (i=cchildren.size()-1) or at the beginning (i=0). For the end case,
      // we are taking F from (and F true), in the beginning case, we are
      // taking F from the original n-ary (and F ...).
      addLfscRule(cdp, cur[0], {cur}, LfscRule::CNF_AND_POS_1, {});
    }
    break;
    default: return false; break;
  }
  return true;
}

void LfscProofPostprocessCallback::addLfscRule(CDProof* cdp, Node conc, const std::vector<Node>& children, LfscRule lr, const std::vector<Node>& args)
{
  std::vector<Node> largs;
  largs.push_back(mkLfscRuleNode(lr));
  largs.push_back(conc);
  largs.insert(largs.end(), args.begin(), args.end());
  cdp->addStep(conc,
                PfRule::LFSC_RULE,
                children,
                largs);
}

Node LfscProofPostprocessCallback::mkChain(Kind k,
                                           const std::vector<Node>& children)
{
  Assert(!children.empty());
  NodeManager* nm = NodeManager::currentNM();
  size_t nchildren = children.size();
  size_t i = 0;
  // do we have a null terminator? If so, we start with it.
  Node ret = LfscTermProcessor::getNullTerminator(k);
  if (ret.isNull())
  {
    ret = children[nchildren - 1];
    i = 1;
  }
  while (i < nchildren)
  {
    ret = nm->mkNode(k, children[(nchildren - 1) - i], ret);
    i++;
  }
  return ret;
}

void LfscProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  ProofNodeUpdater updater(d_pnm, *(d_cb.get()));
  updater.process(pf);
}

}  // namespace proof
}  // namespace CVC4
