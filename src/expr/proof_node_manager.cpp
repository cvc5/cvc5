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

ProofNodeManager::ProofNodeManager(ProofChecker* pc) : d_checker(pc) {}

std::shared_ptr<ProofNode> ProofNodeManager::mkNode(
    ProofStep id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args,
    Node expected)
{
  std::shared_ptr<ProofNode> pn =
      std::make_shared<ProofNode>(id, children, args);
  // compute what pn proves and ensure it matches expected
  if (!checkInternal(pn.get(), expected))
  {
    // if it was invalid, then we return the null node
    return nullptr;
  }
  return pn;
}

bool ProofNodeManager::updateNode(ProofNode* pn,
                                       ProofStep id,
                                       const std::vector<std::shared_ptr<ProofNode>>& children,
                                       const std::vector<Node>& args,
                                       Node expected)
{
  // should have already computed what is proven, and be valid
  Assert(!pn->d_proven.isNull())
      << "ProofNodeManager::updateProofNode: invalid proof provided";
  // either we didn't provide an expected value, or it must match
  if(expected.isNull() || pn->d_proven == expected)
  {
    Assert(false)
      << "ProofNodeManager::checkInternal: provided proof does not match "
         "expected value";
    return false;
  }
  if (expected.isNull())
  {
    expected = pn->d_proven;
  }
  Assert(!expected.isNull());
  pn->setValue(id, children, args);
  // compute what pn proves and ensure it matches expected
  if (!checkInternal(pn.get(), expected))
  {
    // if it was invalid, then we return false
    return false;
  }
  return true;
}

void ProofNodeManager::checkInternal(ProofNode* pn, Node expected)
{
  if (d_checker)
  {
    pn->d_proven = d_checker->check(pn, expected);
    Assert(!pn->d_proven.isNull())
        << "ProofNodeManager::checkInternal: failed to check proof";
  }
  else
  {
    // otherwise we trust the expected value
    Assert(!expected.isNull()) << "ProofNodeManager::checkInternal: no checker "
                                  "or expected value provided";
    pn->d_proven = expected;
  }
}

}  // namespace CVC4
