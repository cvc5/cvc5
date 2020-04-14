/*********************                                                        */
/*! \file proof_node_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof node manager
 **/

#include "expr/proof_node_manager.h"

using namespace CVC4::kind;

namespace CVC4 {

ProofNodeManager::ProofNodeManager(ProofChecker* pc)
    : d_checker(pc)
{
}

std::shared_ptr<ProofNode> ProofNodeManager::mkProofNode(
                  ProofStep id,
                  const std::vector<Node>& children,
                  const std::vector<Node>& args,
                  Node expected)
{
  std::vector<std::shared_ptr<ProofNode>> pn;
  pn = std::make_shared<ProofNode>(id, children, args);
  checkInternal(pn, true, expected);
  return pc;
}

void ProofNodeManager::updateProofNode(ProofNode * pn,                     
                      ProofStep id,
                  const std::vector<Node>& children,
                  const std::vector<Node>& args,
                  Node expected)
{
  // should not change what is proven
  checkInternal(pn, false, expected);
  if (expected.isNull())
  {
    expected = pn->d_proven;
  }
  Assert(!expected.isNull());
  pn->setValue(id, pchildren, args);
  checkInternal(pn, true, expected);
}

void ProofNodeManager::checkInternal(ProofNode * pn,
                    bool doCheck,
                    bool doUpdate,
                    Node expected)
{
  
}
  
}  // namespace CVC4
