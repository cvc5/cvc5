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
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args,
    Node expected)
{
  Node res = checkInternal(id, children, args, expected);
  if (res.isNull())
  {
    // if it was invalid, then we return the null node
    return nullptr;
  }
  // otherwise construct the proof node and set its proven field
  std::shared_ptr<ProofNode> pn =
      std::make_shared<ProofNode>(id, children, args);
  pn->d_proven = res;
  return pn;
}

bool ProofNodeManager::updateNode(
    ProofNode* pn,
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args)
{
  // should have already computed what is proven
  Assert(!pn->d_proven.isNull())
      << "ProofNodeManager::updateProofNode: invalid proof provided";
  // We expect to prove the same thing as before
  Node res = checkInternal(id, children, args, pn->d_proven);
  if (res.isNull())
  {
    // if it was invalid, then we do not update
    return false;
  }
  // we update its value
  pn->setValue(id, children, args);
  // proven field should already be the same as the result
  Assert(res == pn->d_proven);
  return true;
}

Node ProofNodeManager::checkInternal(
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args,
    Node expected)
{
  Node res;
  if (d_checker)
  {
    // check with the checker, which takes expected as argument
    res = d_checker->check(id, children, args, expected);
    Assert(!res.isNull())
        << "ProofNodeManager::checkInternal: failed to check proof";
  }
  else
  {
    // otherwise we trust the expected value, if it exists
    Assert(!expected.isNull()) << "ProofNodeManager::checkInternal: no checker "
                                  "or expected value provided";
    res = expected;
  }
  return res;
}

ProofChecker* ProofNodeManager::getChecker() const { return d_checker; }

}  // namespace CVC4
