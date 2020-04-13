/*********************                                                        */
/*! \file proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof
 **/

#include "expr/proof.h"

using namespace CVC4::kind;

namespace CVC4 {

CDProof(context::Context* c, ProofChecker* pc) : d_checker(pc), d_nodes(c) {}

Node CDProof::registerStep(Node fact,
                           ProofStep id,
                           const std::vector<Node>& children,
                           const std::vector<Node>& args,
                           bool ensureChildren)
{
  NodeProofNodeMap::iterator it = d_nodes.find(fact);
  if (it != d_nodes.end())
  {
    if ((*it).second->getId() != ProofStep::ASSUME || id == ProofStep::ASSUME)
    {
      // already proven or assumed, nothing to do
      return fact;
    }
    // we will overwrite assumption
  }
  
  // collect the child proofs 
  std::vector<std::shared_ptr<ProofNode>> pchildren;
  for (const Node& c : children)
  {
    std::shared_ptr<ProofNode> pc = getProof(c);
    if (pc == nullptr)
    {
      if (ensureChildren)
      {
        // failed to get a proof for a child, fail
        return Node::null();
      }
      // otherwise, we initialize it as an assumption
      std::vector<Node> pcargs = {c};
      std::vector<std::shared_ptr<ProofNode>> pcassume;
      std::shared_ptr<ProofNode> pchild =
          std::make_shared<ProofNode>(ProofStep::ASSUME, pcassume, pcargs);
      d_nodes.insert(c, pchild);
      pchild->d_proven = c;
    }
    pchildren.push_back(pc);
  }

  // create or reinitialize it
  std::shared_ptr<ProofNode> pthis;
  if (it == d_nodes.end())
  {
    pthis = std::make_shared<ProofNode>(id, pchildren, args);
    d_nodes.insert(fact, pthis);
  }
  else
  {
    Assert (pthis->d_proven==fact);
    // overwrite its value
    pthis = (*it).second;
    pthis->setValue(id, pchildren, args);
  }
  // check it
  if (d_checker)
  {
    d_checker->check(pthis.get(), fact);
  }
  else
  {
    pthis->d_proven = fact;
  }
  // must be equal to given fact
  if (fact == pthis->d_proven)
  {
    // valid in this context
    return fact;
  }
  return Node::null();
}

}  // namespace CVC4
