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

using namespace CVC4::kind;

namespace CVC4 {
namespace smt {

ProofPostprocessCallback::ProofPostprocessCallback(ProofNodeManager* pnm)
    : d_pnm(pnm)
{
  // always eliminate macro rules (add to d_elimRules?)
}

void ProofPostprocessCallback::setEliminateRule(PfRule rule) { d_elimRules.insert(rule); }

bool ProofPostprocessCallback::shouldUpdate(ProofNode* pn) { return d_elimRules.find(pn->getRule())!=d_elimRules.end(); }

bool ProofPostprocessCallback::update(PfRule id,
                    const std::vector<Node>& children,
                    const std::vector<Node>& args,
                    CDProof* cdp)
{
  // TODO
  return false;
}

}  // namespace smt
}  // namespace CVC4
