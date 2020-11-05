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

#include "expr/lazy_proof.h"
#include "expr/proof_node_algorithm.h"
#include "expr/proof_node_updater.h"

namespace CVC4 {
namespace proof {

LfscProofPostprocessCallback::LfscProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm)
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
  Assert(id != PfRule::LFSC_RULE);
  // convert arguments to internal form
  std::vector<Node> ias;
  for (const Node& a : args)
  {
    // ias.push_back(
  }

  switch (id)
  {
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
    default: return false; break;
  }
  return true;
}

void LfscProofPostprocess::process(std::shared_ptr<ProofNode> pf) {}

}  // namespace proof
}  // namespace CVC4
