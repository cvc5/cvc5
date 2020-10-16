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

#include "expr/lazy_proof.h"
#include "expr/proof_node_algorithm.h"
#include "expr/proof_node_updater.h"

namespace CVC4 {

namespace proof {

LeanProofPostprocessCallback::LeanProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm)
{
}

LeanProofPostprocess::LeanProofPostprocess(ProofNodeManager* pnm)
    : d_cb(new proof::LeanProofPostprocessCallback(pnm)), d_pnm(pnm)
{
}

bool LeanProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                bool& continueUpdate)
{
  return false;
};

bool LeanProofPostprocessCallback::update(Node res,
                                          PfRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args,
                                          CDProof* cdp,
                                          bool& continueUpdate)
{
  return true;
};

void LeanProofPostprocess::process(std::shared_ptr<ProofNode> pf){};
}  // namespace proof
}  // namespace CVC4
