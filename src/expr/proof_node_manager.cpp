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

std::shared_ptr<ProofNode> ProofNodeManager::mkProofNode(
    ProofStep id,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    Node expected)
{
  std::shared_ptr<ProofNode> pn =
      std::make_shared<ProofNode>(id, children, args);
  // compute what pn proves and ensure it matches expected
  checkInternal(pn.get(), true, expected);
  return pn;
}

void ProofNodeManager::updateProofNode(ProofNode* pn,
                                       ProofStep id,
                                       const std::vector<Node>& children,
                                       const std::vector<Node>& args,
                                       Node expected)
{
  // should have already computed what is proven
  Assert(!pn->d_proven.isNull())
      << "ProofNodeManager::updateProofNode: invalid proof provided";
  // either we didn't provide an expected value, or it matches
  Assert(expected.isNull() || pn->d_proven == expected)
      << "ProofNodeManager::checkInternal: provided proof does not match "
         "expected value";
  // ensure that what pn previously proves matches expected
  checkInternal(pn, false, expected);
  if (expected.isNull())
  {
    expected = pn->d_proven;
  }
  Assert(!expected.isNull());
  pn->setValue(id, pchildren, args);
  // compute what pn proves and ensure it matches expected
  checkInternal(pn, true, expected);
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
